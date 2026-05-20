/**
 * auth-login — strict email/password login.
 *
 * Anti-abuse rules enforced:
 *  1. Suspended accounts are hard-blocked with a clear message
 *  2. Brute-force protection: lock account for 15 min after 5 failed attempts
 *  3. Failed-attempt counter resets on successful login
 *  4. Google-only accounts cannot use password login
 */
const { getPool, ok, err, preflight } = require('./_db');
const bcrypt = require('bcryptjs');

const MAX_ATTEMPTS   = 5;
const LOCKOUT_MINS   = 15;

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try {
    body = JSON.parse(event.body || '{}');
  } catch {
    return err('Invalid JSON', 400);
  }

  const { email, password } = body;
  if (!email || !password) return err('Email and password required.', 400);

  const db = getPool();

  let user;
  try {
    const result = await db.query(
      `SELECT id, name, email, "hashedPassword", is_suspended, suspended_reason,
              login_attempts, login_locked_until
       FROM "User" WHERE email = $1 LIMIT 1`,
      [email.toLowerCase()]
    );
    if (result.rows.length === 0) return err('No account found. Sign up first.', 401);
    user = result.rows[0];
  } catch (e) {
    console.error('[auth-login] db fetch', e.message);
    return err('Server error', 500);
  }

  // ── Hard block suspended accounts ─────────────────────────────────────────
  if (user.is_suspended) {
    return err(
      `Account suspended${user.suspended_reason ? ': ' + user.suspended_reason : ''}. Contact support@ambore.org.`,
      403
    );
  }

  // ── Brute-force lockout check ──────────────────────────────────────────────
  if (user.login_locked_until && new Date(user.login_locked_until) > new Date()) {
    const unlockAt = new Date(user.login_locked_until).toUTCString();
    return err(
      `Account temporarily locked due to too many failed attempts. Try again after ${unlockAt}.`,
      429
    );
  }

  if (!user.hashedPassword) return err('This account uses Google sign-in. Use "Continue with Google".', 401);

  const valid = await bcrypt.compare(password, user.hashedPassword);

  if (!valid) {
    // Increment failed attempt counter; lock if threshold reached
    const attempts = (user.login_attempts || 0) + 1;
    const lockUntil = attempts >= MAX_ATTEMPTS
      ? new Date(Date.now() + LOCKOUT_MINS * 60 * 1000).toISOString()
      : null;

    await db.query(
      `UPDATE "User"
       SET login_attempts = $1,
           login_locked_until = $2
       WHERE id = $3`,
      [attempts, lockUntil, user.id]
    );

    if (lockUntil) {
      return err(
        `Too many failed attempts. Account locked for ${LOCKOUT_MINS} minutes.`,
        429
      );
    }

    const remaining = MAX_ATTEMPTS - attempts;
    return err(
      `Incorrect password. ${remaining} attempt${remaining === 1 ? '' : 's'} remaining before lockout.`,
      401
    );
  }

  // ── Successful login — reset brute-force counters ─────────────────────────
  await db.query(
    `UPDATE "User" SET login_attempts = 0, login_locked_until = NULL WHERE id = $1`,
    [user.id]
  );

  return ok({ userId: user.id, name: user.name, email: user.email });
};
