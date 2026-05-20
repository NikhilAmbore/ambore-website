/**
 * auth-register — strict email/password registration.
 *
 * Security rules:
 *  1. Canonical email dedup — blocks gmail dots, + aliases on ALL providers
 *  2. IP rate limit: max 3 signups per IP per hour
 *  3. Exact + canonical duplicate check before insert
 *  4. Race condition handled: DB unique constraint is the final safety net
 *  5. signup_ip stored for abuse investigation
 */
const { getPool, ok, err, preflight, clientIp, checkIpLimit, logAuthAttempt } = require('./_db');
const bcrypt = require('bcryptjs');

const MAX_SIGNUPS_PER_IP_PER_HOUR = 3;

/**
 * Canonical email: lowercase + strip + aliases + remove Gmail dots.
 * Applies + stripping to ALL providers (not just Gmail).
 */
function canonicalEmail(raw) {
  const lower = (raw || '').toLowerCase().trim();
  const at    = lower.lastIndexOf('@');
  if (at === -1) return lower;

  let local    = lower.slice(0, at).split('+')[0]; // strip + alias for all providers
  const domain = lower.slice(at + 1);

  if (domain === 'gmail.com' || domain === 'googlemail.com') {
    local = local.replace(/\./g, ''); // strip dots for Gmail only
  }

  return `${local}@${domain}`;
}

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { name, email, password } = body;
  if (!name || !email || !password)  return err('All fields required.', 400);
  if (password.length < 8)           return err('Password must be at least 8 characters.', 400);
  if (!/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(email)) return err('Invalid email address.', 400);

  const canonical = canonicalEmail(email);
  const ip        = clientIp(event);
  const db        = getPool();

  // ── IP rate limit: max 3 new accounts per IP per hour ─────────────────────
  const ipBlocked = await checkIpLimit(db, ip, 'signup', MAX_SIGNUPS_PER_IP_PER_HOUR, 60);
  if (ipBlocked.blocked) {
    return err('Too many accounts created from this IP. Try again later.', 429);
  }

  // ── Duplicate check: exact email ──────────────────────────────────────────
  const exactCheck = await db.query(
    'SELECT id FROM "User" WHERE email = $1 LIMIT 1',
    [email.toLowerCase().trim()]
  );
  if (exactCheck.rows.length > 0) return err('An account with that email already exists.', 409);

  // ── Duplicate check: canonical email (catches alias/dot tricks) ────────────
  const canonCheck = await db.query(
    'SELECT id FROM "User" WHERE email_canonical = $1 LIMIT 1',
    [canonical]
  );
  if (canonCheck.rows.length > 0) return err('An account with that email already exists.', 409);

  try {
    const hashedPassword = await bcrypt.hash(password, 10);
    const referralCode   = Math.random().toString(36).substring(2, 10).toUpperCase();

    const result = await db.query(
      `INSERT INTO "User"
         (id, email, email_canonical, name, "hashedPassword", "referralCode", signup_ip, "createdAt", "updatedAt")
       VALUES (gen_random_uuid()::text, $1, $2, $3, $4, $5, $6, NOW(), NOW())
       RETURNING id, name, email`,
      [email.toLowerCase().trim(), canonical, name.trim(), hashedPassword, referralCode, ip]
    );
    const user = result.rows[0];

    // Log signup IP for rate-limiting future attempts
    await logAuthAttempt(db, ip, 'signup');

    await db.query(
      `INSERT INTO "CareerScore" (id, "userId", overall, "resumeScore", "atsScore", "interviewScore", "updatedAt")
       VALUES (gen_random_uuid()::text, $1, 0, 0, 0, 0, NOW()) ON CONFLICT DO NOTHING`,
      [user.id]
    );
    await db.query(
      `INSERT INTO "ActivityLog" (id, "userId", type, "createdAt") VALUES (gen_random_uuid()::text, $1, $2, NOW())`,
      [user.id, 'account_created']
    );

    return ok({ userId: user.id, name: user.name, email: user.email });
  } catch (e) {
    if (e.code === '23505') return err('An account with that email already exists.', 409);
    console.error('[auth-register]', e.message);
    return err('Server error: ' + e.message, 500);
  }
};
