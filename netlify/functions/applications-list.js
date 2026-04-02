const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'GET') return err('Method not allowed', 405);

  const userId = event.queryStringParameters?.userId;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);

  const db = getPool();
  const result = await db.query(
    'SELECT * FROM "Application" WHERE "userId" = $1 ORDER BY "appliedDate" DESC',
    [userId]
  );

  return ok({ applications: result.rows });
};
