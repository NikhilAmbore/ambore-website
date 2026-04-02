const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'GET') return err('Method not allowed', 405);

  const userId = event.queryStringParameters?.userId;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);

  const db = getPool();
  const result = await db.query(
    'SELECT metadata, "createdAt" FROM "ActivityLog" WHERE "userId"=$1 AND type=$2 ORDER BY "createdAt" DESC',
    [userId, 'job_saved']
  );

  const jobs = result.rows.map(r => ({ ...r.metadata, savedAt: r.createdAt }));
  const jobIds = jobs.map(j => j.jobId).filter(Boolean);

  return ok({ jobs, jobIds });
};
