const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { userId, jobId, jobData, action } = body; // action: 'save' or 'unsave'
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);
  if (!jobId) return err('jobId required', 400);

  const db = getPool();

  if (action === 'unsave') {
    await db.query(
      'DELETE FROM "ActivityLog" WHERE "userId"=$1 AND type=$2 AND metadata->>\'jobId\'=$3',
      [userId, 'job_saved', jobId]
    );
    return ok({ saved: false });
  }

  // Save: check if already saved
  const existing = await db.query(
    'SELECT id FROM "ActivityLog" WHERE "userId"=$1 AND type=$2 AND metadata->>\'jobId\'=$3',
    [userId, 'job_saved', jobId]
  );
  if (existing.rows.length === 0) {
    await db.query(
      'INSERT INTO "ActivityLog" (id,"userId",type,metadata,"createdAt") VALUES (gen_random_uuid()::text,$1,$2,$3,NOW())',
      [userId, 'job_saved', JSON.stringify({ jobId, ...(jobData || {}) })]
    );
  }

  return ok({ saved: true });
};
