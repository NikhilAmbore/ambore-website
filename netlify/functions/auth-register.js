const { getPool, ok, err, preflight } = require('./_db');
const bcrypt = require('bcryptjs');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  try {
    const { name, email, password } = JSON.parse(event.body || '{}');
    if (!name || !email || !password) return err('All fields required.', 400);
    if (password.length < 8) return err('Password must be at least 8 characters.', 400);
    if (!/^[^@]+@[^@]+\.[^@]+$/.test(email)) return err('Invalid email address.', 400);

    const db = getPool();

    const existing = await db.query('SELECT id FROM "User" WHERE email = $1', [email.toLowerCase()]);
    if (existing.rows.length > 0) return err('An account with that email already exists.', 409);

    const hashedPassword = await bcrypt.hash(password, 10);
    const referralCode = Math.random().toString(36).substring(2, 10).toUpperCase();
    const result = await db.query(
      'INSERT INTO "User" (id, email, name, "hashedPassword", "referralCode", "createdAt", "updatedAt") VALUES (gen_random_uuid()::text, $1, $2, $3, $4, NOW(), NOW()) RETURNING id, name, email',
      [email.toLowerCase(), name.trim(), hashedPassword, referralCode]
    );
    const user = result.rows[0];

    await db.query(
      'INSERT INTO "CareerScore" (id, "userId", overall, "resumeScore", "atsScore", "interviewScore", "updatedAt") VALUES (gen_random_uuid()::text, $1, 0, 0, 0, 0, NOW()) ON CONFLICT DO NOTHING',
      [user.id]
    );
    await db.query(
      'INSERT INTO "ActivityLog" (id, "userId", type, "createdAt") VALUES (gen_random_uuid()::text, $1, $2, NOW())',
      [user.id, 'account_created']
    );

    return ok({ userId: user.id, name: user.name, email: user.email });
  } catch (e) {
    console.error('[auth-register]', e.message);
    return err('Server error: ' + e.message, 500);
  }
};
