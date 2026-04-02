const { Pool } = require('pg');
const bcrypt = require('bcryptjs');

let pool;
function getPool() {
  if (!pool) pool = new Pool({ connectionString: process.env.DATABASE_URL, ssl: { rejectUnauthorized: false } });
  return pool;
}

exports.handler = async (event) => {
  if (event.httpMethod !== 'POST') return { statusCode: 405, body: 'Method Not Allowed' };
  const headers = {
    'Content-Type': 'application/json',
    'Access-Control-Allow-Origin': 'https://ambore.org',
  };
  try {
    const { name, email, password } = JSON.parse(event.body || '{}');
    if (!name || !email || !password) return { statusCode: 400, headers, body: JSON.stringify({ error: 'All fields required.' }) };
    if (password.length < 8) return { statusCode: 400, headers, body: JSON.stringify({ error: 'Password must be at least 8 characters.' }) };
    if (!/^[^@]+@[^@]+\.[^@]+$/.test(email)) return { statusCode: 400, headers, body: JSON.stringify({ error: 'Invalid email address.' }) };

    const db = getPool();

    // Check existing
    const existing = await db.query('SELECT id FROM "User" WHERE email = $1', [email.toLowerCase()]);
    if (existing.rows.length > 0) return { statusCode: 409, headers, body: JSON.stringify({ error: 'An account with that email already exists.' }) };

    const hashedPassword = await bcrypt.hash(password, 10);
    const referralCode = Math.random().toString(36).substring(2, 10).toUpperCase();
    const result = await db.query(
      'INSERT INTO "User" (id, email, name, "hashedPassword", "referralCode", "createdAt", "updatedAt") VALUES (gen_random_uuid()::text, $1, $2, $3, $4, NOW(), NOW()) RETURNING id, name, email',
      [email.toLowerCase(), name.trim(), hashedPassword, referralCode]
    );
    const user = result.rows[0];

    // Create initial CareerScore row
    await db.query(
      'INSERT INTO "CareerScore" (id, "userId", overall, "resumeScore", "atsScore", "interviewScore", "updatedAt") VALUES (gen_random_uuid()::text, $1, 0, 0, 0, 0, NOW()) ON CONFLICT DO NOTHING',
      [user.id]
    );

    // Log account_created activity
    await db.query(
      'INSERT INTO "ActivityLog" (id, "userId", type, "createdAt") VALUES (gen_random_uuid()::text, $1, $2, NOW())',
      [user.id, 'account_created']
    );

    return { statusCode: 200, headers, body: JSON.stringify({ userId: user.id, name: user.name, email: user.email }) };
  } catch (err) {
    console.error('Register error:', err);
    return { statusCode: 500, headers, body: JSON.stringify({ error: 'Server error. Please try again.' }) };
  }
};
