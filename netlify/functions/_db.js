// Shared DB pool + auth helper for all Netlify functions
const { Pool } = require('pg');

let pool;
function getPool() {
  if (!pool) {
    pool = new Pool({
      connectionString: process.env.DATABASE_URL,
      ssl: { rejectUnauthorized: false }, // required by Neon pooler
      max: 5,
      idleTimeoutMillis: 30000,
      connectionTimeoutMillis: 5000,
      statement_timeout: 8000,                  // kill queries hanging >8s
      idle_in_transaction_session_timeout: 5000, // kill idle transactions >5s
    });
  }
  return pool;
}

const CORS = {
  'Content-Type': 'application/json',
  'Access-Control-Allow-Origin': 'https://ambore.org',
  'Access-Control-Allow-Methods': 'GET, POST, DELETE, OPTIONS',
  'Access-Control-Allow-Headers': 'Content-Type',
};

function ok(data, status = 200) {
  return { statusCode: status, headers: CORS, body: JSON.stringify(data) };
}

function err(msg, status = 400) {
  return { statusCode: status, headers: CORS, body: JSON.stringify({ error: msg }) };
}

function preflight() {
  return { statusCode: 204, headers: CORS, body: '' };
}

// Verify userId — accepts UUID or email (backward compat: old sessions stored email as id)
async function verifyUser(userId) {
  if (!userId) return null;
  const db = getPool();
  try {
    const r = await db.query(
      'SELECT id, name, email FROM "User" WHERE id::text = $1 OR email = $1 LIMIT 1',
      [String(userId).slice(0, 256)]
    );
    return r.rows[0] || null;
  } catch (e) {
    try {
      const r = await db.query(
        'SELECT id, name, email FROM "User" WHERE email = $1 LIMIT 1',
        [String(userId).slice(0, 256)]
      );
      return r.rows[0] || null;
    } catch { return null; }
  }
}

/** Extract real client IP from Netlify function event headers. */
function clientIp(event) {
  return (
    (event.headers['x-forwarded-for'] || '').split(',')[0].trim() ||
    event.headers['client-ip'] ||
    'unknown'
  );
}

/**
 * IP-based rate limit using the AuthAttempt table.
 * Returns { blocked: true } if the IP has exceeded the limit.
 */
async function checkIpLimit(db, ip, type, maxAttempts, windowMinutes) {
  if (!ip || ip === 'unknown') return { blocked: false };
  try {
    const r = await db.query(
      `SELECT COUNT(*) AS cnt FROM "AuthAttempt"
       WHERE ip = $1 AND type = $2
         AND "createdAt" > NOW() - ($3 || ' minutes')::INTERVAL`,
      [ip, type, String(windowMinutes)]
    );
    return { blocked: parseInt(r.rows[0].cnt, 10) >= maxAttempts };
  } catch { return { blocked: false }; }
}

/** Log an auth attempt (fire-and-forget). */
async function logAuthAttempt(db, ip, type) {
  if (!ip || ip === 'unknown') return;
  try {
    await db.query(
      `INSERT INTO "AuthAttempt" (id, ip, type) VALUES (gen_random_uuid()::text, $1, $2)`,
      [ip, type]
    );
  } catch { /* non-critical */ }
}

module.exports = { getPool, ok, err, preflight, verifyUser, CORS, clientIp, checkIpLimit, logAuthAttempt };
