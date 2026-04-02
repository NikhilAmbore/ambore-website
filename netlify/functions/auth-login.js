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
    const { email, password } = JSON.parse(event.body || '{}');
    if (!email || !password) return { statusCode: 400, headers, body: JSON.stringify({ error: 'Email and password required.' }) };

    const db = getPool();
    const result = await db.query('SELECT id, name, email, "hashedPassword" FROM "User" WHERE email = $1', [email.toLowerCase()]);
    if (result.rows.length === 0) return { statusCode: 401, headers, body: JSON.stringify({ error: 'No account found. Sign up first.' }) };

    const user = result.rows[0];
    if (!user.hashedPassword) return { statusCode: 401, headers, body: JSON.stringify({ error: 'This account uses Google sign-in.' }) };

    const valid = await bcrypt.compare(password, user.hashedPassword);
    if (!valid) return { statusCode: 401, headers, body: JSON.stringify({ error: 'Incorrect password.' }) };

    return { statusCode: 200, headers, body: JSON.stringify({ userId: user.id, name: user.name, email: user.email }) };
  } catch (err) {
    console.error('Login error:', err);
    return { statusCode: 500, headers, body: JSON.stringify({ error: 'Server error. Please try again.' }) };
  }
};
