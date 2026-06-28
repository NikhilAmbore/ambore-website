const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'GET') return err('Method not allowed', 405);

  const userId = event.queryStringParameters?.userId;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);

  const page   = Math.max(0, parseInt(event.queryStringParameters?.page  || '0', 10));
  const limit  = Math.min(100, Math.max(1, parseInt(event.queryStringParameters?.limit || '100', 10)));
  const offset = page * limit;

  const db = getPool();
  const [result, countResult] = await Promise.all([
    db.query(
      'SELECT * FROM "Application" WHERE "userId" = $1 ORDER BY "appliedDate" DESC LIMIT $2 OFFSET $3',
      [userId, limit, offset]
    ),
    db.query('SELECT COUNT(*) FROM "Application" WHERE "userId" = $1', [userId]),
  ]);

  const total = parseInt(countResult.rows[0]?.count || 0);
  return ok({ applications: result.rows, total, page, limit });
};
