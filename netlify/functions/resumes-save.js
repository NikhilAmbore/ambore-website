const { getPool, ok, err, preflight, verifyUser } = require('./_db');
const { randomUUID } = require('crypto');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let body;
  try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

  const { userId, id, title, content } = body;
  const user = await verifyUser(userId);
  if (!user) return err('Unauthorized', 401);
  if (!title || !content) return err('title and content required', 400);

  const db = getPool();
  let result;
  if (id) {
    result = await db.query(
      'UPDATE "Resume" SET title=$1, content=$2, "updatedAt"=NOW() WHERE id=$3 AND "userId"=$4 RETURNING id, title, "createdAt", "updatedAt"',
      [title.slice(0, 255), content.slice(0, 100000), id, userId]
    );
    if (result.rows.length === 0) return err('Resume not found', 404);
  } else {
    result = await db.query(
      'INSERT INTO "Resume" (id,"userId",title,content,"createdAt","updatedAt") VALUES ($1,$2,$3,$4,NOW(),NOW()) RETURNING id, title, "createdAt", "updatedAt"',
      [randomUUID(), userId, title.slice(0, 255), content.slice(0, 100000)]
    );
    await db.query(
      'INSERT INTO "ActivityLog" (id,"userId",type,metadata,"createdAt") VALUES (gen_random_uuid()::text,$1,$2,$3,NOW())',
      [userId, 'resume_analyzed', JSON.stringify({ title })]
    );
  }

  return ok({ resume: result.rows[0] });
};
