const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { userId, id } = body;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);
  if (!id) return err('id required', 400);

  const db = getPool();
  await db.query('DELETE FROM "Resume" WHERE id=$1 AND "userId"=$2', [id, userId]);
  return ok({ success: true });
};
