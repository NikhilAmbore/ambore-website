const { getPool, ok, err, preflight } = require('./_db');
const bcrypt = require('bcryptjs');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  try {
    const { email, password } = JSON.parse(event.body || '{}');
    if (!email || !password) return err('Email and password required.', 400);

    const db = getPool();
    const result = await db.query('SELECT id, name, email, "hashedPassword" FROM "User" WHERE email = $1', [email.toLowerCase()]);
    if (result.rows.length === 0) return err('No account found. Sign up first.', 401);

    const user = result.rows[0];
    if (!user.hashedPassword) return err('This account uses Google sign-in.', 401);

    const valid = await bcrypt.compare(password, user.hashedPassword);
    if (!valid) return err('Incorrect password.', 401);

    return ok({ userId: user.id, name: user.name, email: user.email });
  } catch (e) {
    console.error('[auth-login]', e.message);
    return err('Server error: ' + e.message, 500);
  }
};
