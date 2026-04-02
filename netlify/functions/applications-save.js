const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { userId, id, jobTitle, company, location, status, notes, salary, url, jobData, appliedDate } = body;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);
  if (!jobTitle || !company) return err('jobTitle and company required', 400);

  const db = getPool();
  const VALID_STATUSES = ['tracking', 'applied', 'interviewing', 'offer', 'rejected', 'ghosted'];
  const safeStatus = VALID_STATUSES.includes(status) ? status : 'applied';

  let result;
  if (id) {
    // Update existing
    result = await db.query(
      `UPDATE "Application" SET "jobTitle"=$1, company=$2, location=$3, status=$4, notes=$5, salary=$6, url=$7, "jobData"=$8, "updatedAt"=NOW()
       WHERE id=$9 AND "userId"=$10 RETURNING *`,
      [jobTitle, company, location || null, safeStatus, notes || null, salary || null, url || null, jobData ? JSON.stringify(jobData) : null, id, userId]
    );
    if (result.rows.length === 0) return err('Application not found', 404);
  } else {
    // Insert new
    const cuid = require('crypto').randomUUID();
    const aDate = appliedDate ? new Date(appliedDate) : new Date();
    result = await db.query(
      `INSERT INTO "Application" (id, "userId", "jobTitle", company, location, status, notes, salary, url, "jobData", "appliedDate", "createdAt", "updatedAt")
       VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,NOW(),NOW()) RETURNING *`,
      [cuid, userId, jobTitle, company, location || null, safeStatus, notes || null, salary || null, url || null, jobData ? JSON.stringify(jobData) : null, aDate]
    );
    // Log activity
    await db.query(
      'INSERT INTO "ActivityLog" (id,"userId",type,metadata,"createdAt") VALUES (gen_random_uuid()::text,$1,$2,$3,NOW())',
      [userId, 'job_applied', JSON.stringify({ jobTitle, company })]
    );
  }

  return ok({ application: result.rows[0] });
};
