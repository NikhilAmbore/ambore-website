// Shared DB pool + auth helper for all Netlify functions
const { Pool } = require('pg');

let pool;
function getPool() {
  if (!pool) {
    pool = new Pool({
      connectionString: process.env.DATABASE_URL,
      ssl: { rejectUnauthorized: false },
      max: 5,
      idleTimeoutMillis: 30000,
      connectionTimeoutMillis: 5000,
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
    // Try UUID match first, then email fallback in one query
    const r = await db.query(
      'SELECT id, name, email FROM "User" WHERE id::text = $1 OR email = $1',
      [userId]
    );
    return r.rows[0] || null;
  } catch (e) {
    // id::text cast edge case — fall back to email-only
    try {
      const r = await db.query('SELECT id, name, email FROM "User" WHERE email = $1', [userId]);
      return r.rows[0] || null;
    } catch { return null; }
  }
}

module.exports = { getPool, ok, err, preflight, verifyUser, CORS };
