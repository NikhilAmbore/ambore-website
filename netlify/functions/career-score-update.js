const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { userId, resumeScore, atsScore, interviewScore } = body;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);

  const db = getPool();

  // Fetch existing
  const existing = await db.query('SELECT * FROM "CareerScore" WHERE "userId"=$1', [userId]);
  const cur = existing.rows[0] || { resumeScore: 0, atsScore: 0, interviewScore: 0 };

  const newResume = resumeScore !== undefined ? Math.max(0, Math.min(100, resumeScore)) : cur.resumeScore;
  const newAts = atsScore !== undefined ? Math.max(0, Math.min(100, atsScore)) : cur.atsScore;
  const newInterview = interviewScore !== undefined ? Math.max(0, Math.min(100, interviewScore)) : cur.interviewScore;

  // Weighted overall: resume 40%, ats 35%, interview 25%
  const overall = Math.round(newResume * 0.40 + newAts * 0.35 + newInterview * 0.25);

  const result = await db.query(
    `INSERT INTO "CareerScore" (id,"userId",overall,"resumeScore","atsScore","interviewScore","updatedAt")
     VALUES (gen_random_uuid()::text,$1,$2,$3,$4,$5,NOW())
     ON CONFLICT ("userId") DO UPDATE SET overall=$2,"resumeScore"=$3,"atsScore"=$4,"interviewScore"=$5,"updatedAt"=NOW()
     RETURNING *`,
    [userId, overall, newResume, newAts, newInterview]
  );

  if (!result.rows[0]) return err('Failed to update career score', 500);
  return ok({ careerScore: result.rows[0] });
};
