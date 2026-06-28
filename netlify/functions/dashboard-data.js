const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'GET') return err('Method not allowed', 405);

  const userId = event.queryStringParameters?.userId;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);

  const db = getPool();

  const [scoreRes, actRes, resumeRes, appRes, savedRes] = await Promise.all([
    db.query('SELECT * FROM "CareerScore" WHERE "userId" = $1', [userId]),
    db.query('SELECT type, metadata, "createdAt" FROM "ActivityLog" WHERE "userId" = $1 ORDER BY "createdAt" DESC LIMIT 10', [userId]),
    db.query('SELECT id, title, "createdAt", "updatedAt" FROM "Resume" WHERE "userId" = $1 ORDER BY "updatedAt" DESC', [userId]),
    db.query('SELECT COUNT(*) FROM "Application" WHERE "userId" = $1', [userId]),
    db.query('SELECT COUNT(*) FROM "ActivityLog" WHERE "userId" = $1 AND type = $2', [userId, 'job_saved']),
  ]);

  const score = scoreRes.rows[0] || { overall: 0, resumeScore: 0, atsScore: 0, interviewScore: 0 };

  return ok({
    careerScore: {
      overall: score.overall,
      resume: score.resumeScore,
      ats: score.atsScore,
      interview: score.interviewScore,
      updatedAt: score.updatedAt,
    },
    recentActivity: actRes.rows,
    resumeCount: resumeRes.rows.length,
    resumes: resumeRes.rows,
    applicationCount: parseInt(appRes.rows[0]?.count || 0),
    savedJobCount: parseInt(savedRes.rows[0]?.count || 0),
  });
};
