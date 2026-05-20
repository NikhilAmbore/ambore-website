/**
 * auth-register — strict email/password registration.
 *
 * Anti-abuse rules enforced:
 *  1. One account per real inbox — canonical email dedup blocks gmail dot/alias tricks
 *  2. Max 3 signups per IP per hour — prevents mass account creation
 *  3. Password minimum 8 characters
 *  4. Email format validation
 *  5. signup_ip stored for abuse investigation
 */
const { getPool, ok, err, preflight } = require('./_db');
const bcrypt = require('bcryptjs');

const MAX_SIGNUPS_PER_IP_PER_HOUR = 3;

/**
 * Normalise an email to its canonical form so that trick registrations are blocked:
 *  - Lowercase the entire address
 *  - Strip everything after "+" in the local part (alias trick)
 *  - Remove dots from Gmail/Googlemail usernames (dot trick)
 */
function canonicalEmail(raw) {
  const lower = raw.toLowerCase().trim();
  const atIdx = lower.lastIndexOf('@');
  if (atIdx === -1) return lower;

  let local  = lower.slice(0, atIdx);
  const domain = lower.slice(atIdx + 1);

  // Strip + alias
  local = local.split('+')[0];

  // Remove dots for Gmail (and googlemail.com alias)
  if (domain === 'gmail.com' || domain === 'googlemail.com') {
    local = local.replace(/\./g, '');
  }

  return `${local}@${domain}`;
}

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try {
    body = JSON.parse(event.body || '{}');
  } catch {
    return err('Invalid JSON', 400);
  }

  const { name, email, password } = body;
  if (!name || !email || !password) return err('All fields required.', 400);
  if (password.length < 8)         return err('Password must be at least 8 characters.', 400);
  if (!/^[^@]+@[^@]+\.[^@]+$/.test(email)) return err('Invalid email address.', 400);

  const canonical = canonicalEmail(email);
  const ip = (
    (event.headers['x-forwarded-for'] || '').split(',')[0].trim() ||
    event.headers['client-ip'] ||
    'unknown'
  );

  const db = getPool();

  // ── IP rate limit: max 3 new accounts per IP per hour ─────────────────────
  if (ip !== 'unknown') {
    const ipCheck = await db.query(
      `SELECT COUNT(*) AS cnt FROM "User"
       WHERE signup_ip = $1 AND "createdAt" > NOW() - INTERVAL '1 hour'`,
      [ip]
    );
    if (parseInt(ipCheck.rows[0].cnt, 10) >= MAX_SIGNUPS_PER_IP_PER_HOUR) {
      return err('Too many accounts created from this IP. Try again later.', 429);
    }
  }

  // ── Exact email duplicate check ────────────────────────────────────────────
  const exactCheck = await db.query(
    'SELECT id FROM "User" WHERE email = $1 LIMIT 1',
    [email.toLowerCase()]
  );
  if (exactCheck.rows.length > 0) {
    return err('An account with that email already exists.', 409);
  }

  // ── Canonical email duplicate check (catches gmail dots/aliases) ───────────
  const canonCheck = await db.query(
    'SELECT id FROM "User" WHERE email_canonical = $1 LIMIT 1',
    [canonical]
  );
  if (canonCheck.rows.length > 0) {
    return err('An account with that email already exists.', 409);
  }

  try {
    const hashedPassword = await bcrypt.hash(password, 10);
    const referralCode   = Math.random().toString(36).substring(2, 10).toUpperCase();

    const result = await db.query(
      `INSERT INTO "User"
         (id, email, email_canonical, name, "hashedPassword", "referralCode",
          signup_ip, "createdAt", "updatedAt")
       VALUES
         (gen_random_uuid()::text, $1, $2, $3, $4, $5, $6, NOW(), NOW())
       RETURNING id, name, email`,
      [email.toLowerCase(), canonical, name.trim(), hashedPassword, referralCode, ip]
    );
    const user = result.rows[0];

    await db.query(
      `INSERT INTO "CareerScore" (id, "userId", overall, "resumeScore", "atsScore", "interviewScore", "updatedAt")
       VALUES (gen_random_uuid()::text, $1, 0, 0, 0, 0, NOW())
       ON CONFLICT DO NOTHING`,
      [user.id]
    );
    await db.query(
      `INSERT INTO "ActivityLog" (id, "userId", type, "createdAt")
       VALUES (gen_random_uuid()::text, $1, $2, NOW())`,
      [user.id, 'account_created']
    );

    return ok({ userId: user.id, name: user.name, email: user.email });
  } catch (e) {
    // Unique constraint violation (race condition) — treat as duplicate
    if (e.code === '23505') return err('An account with that email already exists.', 409);
    console.error('[auth-register]', e.message);
    return err('Server error: ' + e.message, 500);
  }
};
