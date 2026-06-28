/**
 * auth-google — Google OAuth sign-in / sign-up.
 *
 * Security rules:
 *  1. Suspended accounts hard-blocked before any action
 *  2. Canonical email dedup — same normalisation as auth-register
 *  3. IP rate limit: max 3 new Google accounts per IP per hour
 *  4. DB unique constraint is final safety net for race conditions
 *  5. signup_ip and email_canonical stored on first creation
 */
const { getPool, ok, err, preflight, clientIp, checkIpLimit, logAuthAttempt } = require('./_db');

function canonicalEmail(raw) {
  const lower = (raw || '').toLowerCase().trim();
  const at    = lower.lastIndexOf('@');
  if (at === -1) return lower;
  let local    = lower.slice(0, at).split('+')[0];
  const domain = lower.slice(at + 1);
  if (domain === 'gmail.com' || domain === 'googlemail.com') {
    local = local.replace(/\./g, '');
  }
  return `${local}@${domain}`;
}

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { email, name, picture } = body;
  if (!email) return err('Email required.', 400);

  const canonical = canonicalEmail(email);
  const ip        = clientIp(event);
  const db        = getPool();

  // ── Check existing account by exact OR canonical email ────────────────────
  const existing = await db.query(
    `SELECT id, name, email, is_suspended, suspended_reason
     FROM "User" WHERE email = $1 OR email_canonical = $2 LIMIT 1`,
    [email.toLowerCase().trim(), canonical]
  );

  let user;
  if (existing.rows.length > 0) {
    user = existing.rows[0];

    // ── Suspended — hard block ─────────────────────────────────────────────
    if (user.is_suspended) {
      return err(
        `Account suspended${user.suspended_reason ? ': ' + user.suspended_reason : ''}. Contact support@offerly.org.`,
        403
      );
    }

    await db.query(
      `UPDATE "User" SET name = $1, image = $2, "updatedAt" = NOW() WHERE id = $3`,
      [name || user.name, picture || '', user.id]
    );
  } else {
    // ── New Google user — check IP rate limit first ────────────────────────
    const ipBlocked = await checkIpLimit(db, ip, 'signup', 3, 60);
    if (ipBlocked.blocked) {
      return err('Too many accounts created from this IP. Try again later.', 429);
    }

    try {
      const referralCode = Math.random().toString(36).substring(2, 10).toUpperCase();
      const result = await db.query(
        `INSERT INTO "User"
           (id, email, email_canonical, name, image, "referralCode", signup_ip, "createdAt", "updatedAt")
         VALUES (gen_random_uuid()::text, $1, $2, $3, $4, $5, $6, NOW(), NOW())
         RETURNING id, name, email`,
        [email.toLowerCase().trim(), canonical, name || email, picture || '', referralCode, ip]
      );
      user = result.rows[0];

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
    } catch (e) {
      if (e.code === '23505') return err('An account with that email already exists.', 409);
      console.error('[auth-google]', e.message);
      return err('Server error: ' + e.message, 500);
    }
  }

  return ok({ userId: user.id, name: user.name, email: user.email });
};
