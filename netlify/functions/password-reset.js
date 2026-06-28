const { getPool, ok, err, preflight, clientIp, checkIpLimit } = require('./_db');
const bcrypt = require('bcryptjs');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { email, password } = body;
  if (!email || !password) return err('Email and password required.', 400);
  if (password.length < 8)  return err('Password must be at least 8 characters.', 400);

  const ip = clientIp(event);
  const db = getPool();

  // IP rate limit — max 5 resets per IP per 15 minutes
  const ipBlocked = await checkIpLimit(db, ip, 'password_reset', 5, 15);
  if (ipBlocked.blocked) {
    return err('Too many reset attempts. Please wait 15 minutes and try again.', 429);
  }

  try {
    const result = await db.query(
      'SELECT id FROM "User" WHERE email = $1 LIMIT 1',
      [email.toLowerCase().trim()]
    );

    // Always return the same message to avoid email enumeration
    if (result.rows.length === 0) {
      return ok({ success: true, message: 'If an account exists for that email, the password has been updated.' });
    }

    const userId = result.rows[0].id;
    const hashedPassword = await bcrypt.hash(password, 10);

    await db.query(
      `UPDATE "User" SET "hashedPassword"=$1, login_attempts=0, login_locked_until=NULL, "updatedAt"=NOW() WHERE id=$2`,
      [hashedPassword, userId]
    );

    // Log the reset attempt for abuse tracking
    await db.query(
      `INSERT INTO "AuthAttempt" (id, ip, type) VALUES (gen_random_uuid()::text, $1, $2)`,
      [ip, 'password_reset']
    );

    return ok({ success: true, message: 'Password updated successfully. You can now log in.' });
  } catch (e) {
    console.error('[password-reset]', e.message);
    return err('Server error. Please try again.', 500);
  }
};
