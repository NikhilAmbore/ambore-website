const { getPool, ok, err, preflight } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  try {
    const { email, name, picture } = JSON.parse(event.body || '{}');
    if (!email) return err('Email required.', 400);

    const db = getPool();
    const existing = await db.query('SELECT id, name, email FROM "User" WHERE email = $1', [email.toLowerCase()]);

    let user;
    if (existing.rows.length > 0) {
      user = existing.rows[0];
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

    return ok({ userId: user.id, name: user.name, email: user.email });
  } catch (e) {
    console.error('[auth-google]', e.message);
    return err('Server error: ' + e.message, 500);
  }
};
