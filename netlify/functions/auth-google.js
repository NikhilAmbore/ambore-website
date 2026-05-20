/**
 * auth-google — Google OAuth sign-in / sign-up.
 *
 * Anti-abuse rules enforced:
 *  1. Suspended accounts are hard-blocked
 *  2. Canonical email dedup — a Gmail address registered via email/password
 *     cannot be re-registered via Google (and vice versa)
 *  3. Existing account is returned as-is (no duplicate user created)
 *  4. signup_ip and email_canonical stored on first creation
 */
const { getPool, ok, err, preflight } = require('./_db');

function canonicalEmail(raw) {
  const lower = raw.toLowerCase().trim();
  const atIdx = lower.lastIndexOf('@');
  if (atIdx === -1) return lower;
  let local    = lower.slice(0, atIdx).split('+')[0];
  const domain = lower.slice(atIdx + 1);
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

  const { email, name, picture } = body;
  if (!email) return err('Email required.', 400);

  const canonical = canonicalEmail(email);
  const ip = (
    (event.headers['x-forwarded-for'] || '').split(',')[0].trim() ||
    event.headers['client-ip'] ||
    'unknown'
  );

  const db = getPool();

  // ── Check for existing account by exact OR canonical email ────────────────
  const existing = await db.query(
    `SELECT id, name, email, is_suspended, suspended_reason
     FROM "User"
     WHERE email = $1 OR email_canonical = $2
     LIMIT 1`,
    [email.toLowerCase(), canonical]
  );

  let user;
  if (existing.rows.length > 0) {
    user = existing.rows[0];

    // Hard block suspended accounts
    if (user.is_suspended) {
      return err(
        `Account suspended${user.suspended_reason ? ': ' + user.suspended_reason : ''}. Contact support@ambore.org.`,
        403
      );
    }

    // Update name/avatar but never change email or canonical
    await db.query(
      `UPDATE "User" SET name = $1, image = $2, "updatedAt" = NOW() WHERE id = $3`,
      [name || user.name, picture || '', user.id]
    );
  } else {
    // ── New Google user — create account ──────────────────────────────────
    const referralCode = Math.random().toString(36).substring(2, 10).toUpperCase();
    try {
      const result = await db.query(
        `INSERT INTO "User"
           (id, email, email_canonical, name, image, "referralCode", signup_ip, "createdAt", "updatedAt")
         VALUES
           (gen_random_uuid()::text, $1, $2, $3, $4, $5, $6, NOW(), NOW())
         RETURNING id, name, email`,
        [email.toLowerCase(), canonical, name || email, picture || '', referralCode, ip]
      );
      user = result.rows[0];

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
    } catch (e) {
      if (e.code === '23505') return err('An account with that email already exists.', 409);
      console.error('[auth-google]', e.message);
      return err('Server error: ' + e.message, 500);
    }
  }

  return ok({ userId: user.id, name: user.name, email: user.email });
};
