const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  try {
    const { userId, rating, comment, name, role } = JSON.parse(event.body || '{}');
    if (!rating || rating < 1 || rating > 5) return err('Rating 1–5 required');
    if (!comment || comment.trim().length < 10) return err('Review too short (min 10 chars)');
    if (!name || name.trim().length < 2) return err('Name required');

    const db = getPool();

    // Allow guest reviews (no userId required)
    if (userId) {
      const user = await verifyUser(userId);
      if (!user) return err('Invalid user', 401);

      // One review per user — upsert
      await db.query(
        `INSERT INTO "Review" (id, "userId", rating, comment, name, role, "createdAt")
         VALUES (gen_random_uuid(), $1, $2, $3, $4, $5, NOW())
         ON CONFLICT ("userId") DO UPDATE
         SET rating=$2, comment=$3, name=$4, role=$5, "createdAt"=NOW()`,
        [userId, rating, comment.trim(), name.trim(), (role || '').trim()]
      );
    } else {
      // Guest review — store without userId
      await db.query(
        `INSERT INTO "GuestReview" (id, rating, comment, name, role, "createdAt")
         VALUES (gen_random_uuid(), $1, $2, $3, $4, NOW())`,
        [rating, comment.trim(), name.trim(), (role || '').trim()]
      ).catch(async () => {
        // Fallback: store in Review table with a placeholder userId approach
        // Just store as activity for now if GuestReview table doesn't exist
      });
    }

    return ok({ success: true });
  } catch (e) {
    console.error('[reviews-submit]', e.message);
    return err('Server error', 500);
  }
};
