const { getPool, ok, err, preflight, verifyUser } = require('./_db');

const VALID_TYPES = new Set([
  'account_created','resume_analyzed','job_saved','job_applied',
  'interview_practiced','score_updated','cover_letter_generated',
  'linkedin_optimized','resume_saved'
]);

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { userId, type, metadata } = body;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);
  if (!VALID_TYPES.has(type)) return err('Invalid activity type', 400);

  const db = getPool();
  await db.query(
    'INSERT INTO "ActivityLog" (id,"userId",type,metadata,"createdAt") VALUES (gen_random_uuid()::text,$1,$2,$3,NOW())',
    [userId, type, metadata ? JSON.stringify(metadata) : null]
  );

  return ok({ success: true });
};
