const { Pool } = require('pg');

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
    const { email, name, picture } = JSON.parse(event.body || '{}');
    if (!email) return { statusCode: 400, headers, body: JSON.stringify({ error: 'Email required.' }) };

    const db = getPool();
    const existing = await db.query('SELECT id, name, email FROM "User" WHERE email = $1', [email.toLowerCase()]);

    let user;
    if (existing.rows.length > 0) {
      user = existing.rows[0];
      // Update name/image if changed
      await db.query('UPDATE "User" SET name = $1, image = $2, "updatedAt" = NOW() WHERE id = $3', [name || user.name, picture || '', user.id]);
    } else {
      const referralCode = Math.random().toString(36).substring(2, 10).toUpperCase();
      const result = await db.query(
        'INSERT INTO "User" (id, email, name, image, "referralCode", "createdAt", "updatedAt") VALUES (gen_random_uuid()::text, $1, $2, $3, $4, NOW(), NOW()) RETURNING id, name, email',
        [email.toLowerCase(), name || email, picture || '', referralCode]
      );
      user = result.rows[0];

      await db.query(
        'INSERT INTO "CareerScore" (id, "userId", overall, "resumeScore", "atsScore", "interviewScore", "updatedAt") VALUES (gen_random_uuid()::text, $1, 0, 0, 0, 0, NOW()) ON CONFLICT DO NOTHING',
        [user.id]
      );
      await db.query(
        'INSERT INTO "ActivityLog" (id, "userId", type, "createdAt") VALUES (gen_random_uuid()::text, $1, $2, NOW())',
        [user.id, 'account_created']
      );
    }

    return { statusCode: 200, headers, body: JSON.stringify({ userId: user.id, name: user.name, email: user.email }) };
  } catch (err) {
    console.error('Google auth error:', err);
    return { statusCode: 500, headers, body: JSON.stringify({ error: 'Server error. Please try again.' }) };
  }
};
