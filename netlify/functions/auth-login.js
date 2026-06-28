/**
 * auth-login — strict email/password login.
 *
 * Security rules:
 *  1. IP rate limit: max 20 failed attempts per IP per 5 minutes (blocks distributed attacks)
 *  2. Per-account lockout: 5 wrong passwords → 15-min lock
 *  3. Suspended accounts hard-blocked before any password check
 *  4. Failed attempts logged to AuthAttempt table for IP tracking
 *  5. Counter reset on successful login
 */
const { getPool, ok, err, preflight, clientIp, checkIpLimit, logAuthAttempt } = require('./_db');
const bcrypt = require('bcryptjs');

const MAX_ACCOUNT_ATTEMPTS = 5;
const LOCKOUT_MINS         = 15;
const IP_MAX_FAILS         = 20;   // failed logins per IP
const IP_WINDOW_MINS       = 5;    // within this many minutes

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { email, password } = body;
  if (!email || !password) return err('Email and password required.', 400);

  const ip = clientIp(event);
  const db = getPool();

  // ── IP rate limit — block IPs that have failed too many times ─────────────
  const ipBlocked = await checkIpLimit(db, ip, 'login_fail', IP_MAX_FAILS, IP_WINDOW_MINS);
  if (ipBlocked.blocked) {
    return err(`Too many failed login attempts from this IP. Wait ${IP_WINDOW_MINS} minutes.`, 429);
  }

  let user;
  try {
    const result = await db.query(
      `SELECT id, name, email, "hashedPassword", is_suspended, suspended_reason,
              login_attempts, login_locked_until
       FROM "User" WHERE email = $1 LIMIT 1`,
      [email.toLowerCase().trim()]
    );
    if (result.rows.length === 0) {
      // Log attempt even for unknown email — prevents enumeration timing diff
      await logAuthAttempt(db, ip, 'login_fail');
      return err('No account found. Sign up first.', 401);
    }
    user = result.rows[0];
  } catch (e) {
    console.error('[auth-login] db fetch', e.message);
    return err('Server error', 500);
  }

  // ── Suspended ─────────────────────────────────────────────────────────────
  if (user.is_suspended) {
    return err(
      `Account suspended${user.suspended_reason ? ': ' + user.suspended_reason : ''}. Contact support@astraoffer.org.`,
      403
    );
  }

  // ── Per-account lockout ───────────────────────────────────────────────────
  if (user.login_locked_until && new Date(user.login_locked_until) > new Date()) {
    const unlockAt = new Date(user.login_locked_until).toUTCString();
    return err(`Account locked due to too many failed attempts. Try again after ${unlockAt}.`, 429);
  }

  if (!user.hashedPassword) {
    return err('This account uses Google sign-in. Use "Continue with Google".', 401);
  }

  const valid = await bcrypt.compare(password, user.hashedPassword);

  if (!valid) {
    // Log IP-level fail
    await logAuthAttempt(db, ip, 'login_fail');

    // Increment per-account counter
    const attempts  = (user.login_attempts || 0) + 1;
    const lockUntil = attempts >= MAX_ACCOUNT_ATTEMPTS
      ? new Date(Date.now() + LOCKOUT_MINS * 60 * 1000).toISOString()
      : null;

    await db.query(
      `UPDATE "User" SET login_attempts = $1, login_locked_until = $2 WHERE id = $3`,
      [attempts, lockUntil, user.id]
    );

    if (lockUntil) return err(`Too many failed attempts. Account locked for ${LOCKOUT_MINS} minutes.`, 429);

    const remaining = MAX_ACCOUNT_ATTEMPTS - attempts;
    return err(`Incorrect password. ${remaining} attempt${remaining === 1 ? '' : 's'} remaining before lockout.`, 401);
  }

  // ── Success — reset all counters ──────────────────────────────────────────
  await db.query(
    `UPDATE "User" SET login_attempts = 0, login_locked_until = NULL WHERE id = $1`,
    [user.id]
  );

  return ok({ userId: user.id, name: user.name, email: user.email });
};
