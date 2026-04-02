const { getPool, ok, err, preflight } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'GET') return err('Method not allowed', 405);

  try {
    const db = getPool();
    const result = await db.query(
      `SELECT id, rating, comment, name, role, "createdAt"
       FROM "Review"
       ORDER BY "createdAt" DESC
       LIMIT 50`
    );
    return ok({ reviews: result.rows });
  } catch (e) {
    console.error('[reviews-list]', e.message);
    return ok({ reviews: [] }); // graceful fallback
  }
};
