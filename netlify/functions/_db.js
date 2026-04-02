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

// Verify userId belongs to a real user — basic auth check
async function verifyUser(userId) {
  if (!userId) return null;
  const db = getPool();
  const r = await db.query('SELECT id, name, email FROM "User" WHERE id = $1', [userId]);
  return r.rows[0] || null;
}

module.exports = { getPool, ok, err, preflight, verifyUser, CORS };
