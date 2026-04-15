/**
 * Ambore — Live Copilot Meeting Notes Function
 * POST → save / upsert generated notes for a session
 * GET  ?sessionId= → retrieve notes by session
 * GET  ?token=     → retrieve notes by public share token
 */
const { getPool, ok, err, preflight } = require('./_db');
const crypto = require('crypto');

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

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();

  try {
    const db = getPool();

    // ── POST: save notes ───────────────────────────────────────────────────────
    if (event.httpMethod === 'POST') {
      let body;
      try { body = JSON.parse(event.body || '{}'); } catch { return err('Invalid JSON', 400); }

      const { sessionId, userId, notesJson } = body;
      if (!sessionId || !notesJson) return err('sessionId and notesJson required', 400);

      const user = await verifyUserFlex(db, userId);
      if (!user) return err('Unauthorized', 401);

      // Verify session belongs to this user
      const check = await db.query(
        'SELECT id FROM copilot_sessions WHERE id=$1 AND user_id=$2',
        [sessionId, user.id]
      );
      if (!check.rows[0]) return err('Session not found', 404);

      // Upsert
      const existing = await db.query(
        'SELECT id, share_token FROM meeting_notes WHERE session_id=$1',
        [sessionId]
      );

      if (existing.rows[0]) {
        await db.query(
          'UPDATE meeting_notes SET notes_json=$1 WHERE session_id=$2',
          [JSON.stringify(notesJson), sessionId]
        );
        return ok({ notesId: existing.rows[0].id, shareToken: existing.rows[0].share_token });
      }

      const shareToken = crypto.randomBytes(32).toString('hex');
      const r = await db.query(
        `INSERT INTO meeting_notes (session_id, user_id, notes_json, share_token)
         VALUES ($1,$2,$3,$4)
         RETURNING id, share_token`,
        [sessionId, user.id, JSON.stringify(notesJson), shareToken]
      );
      return ok({ notesId: r.rows[0].id, shareToken: r.rows[0].share_token });
    }

    // ── GET: retrieve notes ────────────────────────────────────────────────────
    if (event.httpMethod === 'GET') {
      const p = event.queryStringParameters || {};

      let r;
      if (p.token) {
        r = await db.query(
          `SELECT n.id, n.notes_json, n.share_token, n.created_at,
                  s.company_name, s.job_title, s.started_at, s.duration_seconds,
                  s.full_transcript
           FROM meeting_notes n
           JOIN copilot_sessions s ON s.id = n.session_id
           WHERE n.share_token = $1`,
          [p.token]
        );
      } else if (p.sessionId) {
        r = await db.query(
          `SELECT n.id, n.notes_json, n.share_token, n.created_at,
                  s.company_name, s.job_title, s.started_at, s.duration_seconds,
                  s.full_transcript
           FROM meeting_notes n
           JOIN copilot_sessions s ON s.id = n.session_id
           WHERE n.session_id = $1`,
          [p.sessionId]
        );
      } else {
        return err('sessionId or token required', 400);
      }

      if (!r.rows[0]) return err('Notes not found', 404);
      return ok({ notes: r.rows[0] });
    }

    return err('Method not allowed', 405);

  } catch (e) {
    console.error('[copilot-notes] unhandled error:', e.message);
    return err('Server error: ' + e.message, 500);
  }
};
