/**
 * Ambore — Live Copilot Session Function
 * POST action=resolve → return real UUID for an email-based session
 * POST action=create  → start a new session
 * POST action=end     → end session + save transcript
 * POST action=log     → log an AI interaction
 * GET  ?userId=       → list user's past sessions
 * GET  ?sessionId=    → get single session
 */
const { getPool, ok, err, preflight } = require('./_db');

// Accepts UUID or email — handles old sessions where id was stored as email
async function verifyUserFlex(db, userId) {
  if (!userId) return null;
  try {
    const r = await db.query(
      `SELECT id, name, email FROM "User" WHERE id::text = $1 OR email = $1`,
      [userId]
    );
    return r.rows[0] || null;
  } catch (e) {
    try {
      const r = await db.query(`SELECT id, name, email FROM "User" WHERE email = $1`, [userId]);
      return r.rows[0] || null;
    } catch { return null; }
  }
}

// Run each table creation separately — avoids compound-query failures
// Use TEXT for user_id (Prisma cuid IDs are TEXT, not UUID)
async function ensureTables(db) {
  await db.query(`
    CREATE TABLE IF NOT EXISTS copilot_sessions (
      id               TEXT PRIMARY KEY DEFAULT gen_random_uuid()::text,
      user_id          TEXT,
      job_title        VARCHAR(255),
      company_name     VARCHAR(255),
      resume_text      TEXT,
      job_description  TEXT,
      status           VARCHAR(20) DEFAULT 'active',
      started_at       TIMESTAMP DEFAULT NOW(),
      ended_at         TIMESTAMP,
      duration_seconds INTEGER,
      full_transcript  TEXT,
      created_at       TIMESTAMP DEFAULT NOW()
    )
  `);
  await db.query(`
    CREATE TABLE IF NOT EXISTS copilot_interactions (
      id            TEXT PRIMARY KEY DEFAULT gen_random_uuid()::text,
      session_id    TEXT,
      action_type   VARCHAR(50) NOT NULL,
      user_question TEXT,
      ai_response   TEXT,
      created_at    TIMESTAMP DEFAULT NOW()
    )
  `);
  await db.query(`
    CREATE TABLE IF NOT EXISTS meeting_notes (
      id          TEXT PRIMARY KEY DEFAULT gen_random_uuid()::text,
      session_id  TEXT,
      user_id     TEXT,
      notes_json  JSONB NOT NULL,
      share_token VARCHAR(64) UNIQUE,
      created_at  TIMESTAMP DEFAULT NOW()
    )
  `);
}

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();

  try {
    const db = getPool();

    // Ensure tables exist on first call — errors are non-fatal
    try { await ensureTables(db); } catch (e) {
      console.error('[copilot-session] ensureTables:', e.message);
    }

    // ── POST ───────────────────────────────────────────────────────────────────
    if (event.httpMethod === 'POST') {
      let body;
      try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

      const { action, userId } = body;
      const user = await verifyUserFlex(db, userId);
      if (!user) return err('Unauthorized', 401);

      // Resolve real UUID from email (frontend auto-patch)
      if (action === 'resolve') {
        return ok({ actualUserId: user.id });
      }

      // Create new session
      if (action === 'create') {
        const { company = '', role = '', resume = '', jd = '' } = body;
        const r = await db.query(
          `INSERT INTO copilot_sessions
             (user_id, company_name, job_title, resume_text, job_description)
           VALUES ($1,$2,$3,$4,$5)
           RETURNING id, started_at`,
          [user.id, company, role, resume.slice(0, 12000), jd.slice(0, 6000)]
        );
        return ok({
          sessionId   : r.rows[0].id,
          startedAt   : r.rows[0].started_at,
          actualUserId: user.id
        });
      }

      // End session + save transcript
      if (action === 'end') {
        const { sessionId, transcript = '', duration = 0 } = body;
        if (!sessionId) return err('sessionId required', 400);
        await db.query(
          `UPDATE copilot_sessions
           SET status='completed', ended_at=NOW(),
               duration_seconds=$1, full_transcript=$2
           WHERE id=$3 AND user_id=$4`,
          [duration, transcript.slice(0, 60000), sessionId, user.id]
        );
        return ok({ success: true });
      }

      // Log AI interaction
      if (action === 'log') {
        const { sessionId, actionType, userQuestion = '', aiResponse = '' } = body;
        if (!sessionId || !actionType) return err('sessionId and actionType required', 400);
        await db.query(
          `INSERT INTO copilot_interactions
             (session_id, action_type, user_question, ai_response)
           VALUES ($1,$2,$3,$4)`,
          [sessionId, actionType, userQuestion.slice(0, 2000), aiResponse.slice(0, 8000)]
        );
        return ok({ success: true });
      }

      return err('Unknown action', 400);
    }

    // ── GET ────────────────────────────────────────────────────────────────────
    if (event.httpMethod === 'GET') {
      const p = event.queryStringParameters || {};

      if (p.sessionId) {
        const r = await db.query(
          `SELECT s.id, s.company_name, s.job_title, s.status,
                  s.started_at, s.ended_at, s.duration_seconds,
                  s.resume_text, s.job_description,
                  n.id AS notes_id, n.share_token
           FROM copilot_sessions s
           LEFT JOIN meeting_notes n ON n.session_id = s.id
           WHERE s.id = $1`,
          [p.sessionId]
        );
        if (!r.rows[0]) return err('Session not found', 404);
        return ok({ session: r.rows[0] });
      }

      const user = await verifyUserFlex(db, p.userId);
      if (!user) return err('Unauthorized', 401);

      const r = await db.query(
        `SELECT s.id, s.company_name, s.job_title, s.status,
                s.started_at, s.ended_at, s.duration_seconds,
                n.id AS notes_id, n.share_token
         FROM copilot_sessions s
         LEFT JOIN meeting_notes n ON n.session_id = s.id
         WHERE s.user_id = $1
         ORDER BY s.started_at DESC
         LIMIT 25`,
        [user.id]
      );
      return ok({ sessions: r.rows });
    }

    return err('Method not allowed', 405);

  } catch (e) {
    console.error('[copilot-session] unhandled error:', e.message);
    return err('Server error: ' + e.message, 500);
  }
};
