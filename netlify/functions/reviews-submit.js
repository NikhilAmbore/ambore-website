const { getPool, ok, err, preflight } = require('./_db');

// Make userId nullable on first run (one-time migration)
let migrated = false;
async function ensureNullable(db) {
  if (migrated) return;
  try {
    await db.query(`ALTER TABLE "Review" ALTER COLUMN "userId" DROP NOT NULL`);
  } catch(e) { /* already nullable or no permission — ignore */ }
  migrated = true;
}

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  try {
    const { userId, rating, comment, name, role } = JSON.parse(event.body || '{}');
    if (!rating || rating < 1 || rating > 5) return err('Rating 1–5 required');
    if (!comment || comment.trim().length < 10) return err('Review too short (min 10 chars)');
    if (!name || name.trim().length < 2) return err('Name required');

    const db = getPool();
    await ensureNullable(db);

    if (userId) {
      // Logged-in user — upsert
      const existing = await db.query('SELECT id FROM "Review" WHERE "userId" = $1', [userId]);
      if (existing.rows.length > 0) {
        await db.query(
          `UPDATE "Review" SET rating=$2, comment=$3, name=$4, role=$5, "createdAt"=NOW() WHERE "userId"=$1`,
          [userId, rating, comment.trim(), name.trim(), (role || '').trim()]
        );
      } else {
        await db.query(
          `INSERT INTO "Review" (id, "userId", rating, comment, name, role, "createdAt")
           VALUES (gen_random_uuid(), $1, $2, $3, $4, $5, NOW())`,
          [userId, rating, comment.trim(), name.trim(), (role || '').trim()]
        );
      }
    } else {
      // Guest — NULL userId
      await db.query(
        `INSERT INTO "Review" (id, rating, comment, name, role, "createdAt")
         VALUES (gen_random_uuid(), $1, $2, $3, $4, NOW())`,
        [rating, comment.trim(), name.trim(), (role || '').trim()]
      );
    }

    return ok({ success: true });
  } catch (e) {
    console.error('[reviews-submit]', e.message);
    return err('Server error: ' + e.message, 500);
  }
};
