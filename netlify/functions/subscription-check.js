/**
 * subscription-check — called by claude-proxy before every AI request.
 *
 * Security guarantees:
 *  - FAIL CLOSED: any DB error blocks the call (no fail-open)
 *  - ATOMIC increment: check + increment in one SQL statement, no race condition
 *  - Suspended accounts hard-blocked
 *  - Subscription expiry hard-checked server-side
 *  - Rolling 30-day window reset is also atomic
 */
const { getPool, preflight } = require('./_db');

const PREMIUM_LIMIT = 1000; // AI calls per rolling 30-day window

const FREE_ACCESS_EMAILS = new Set([
  'amborenikhil46@gmail.com',
]);

const CORS = {
  'Content-Type': 'application/json',
  'Access-Control-Allow-Origin': 'https://ambore.org',
  'Access-Control-Allow-Methods': 'POST, OPTIONS',
  'Access-Control-Allow-Headers': 'Content-Type',
};

function respond(data, status = 200) {
  return { statusCode: status, headers: CORS, body: JSON.stringify(data) };
}

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return respond({ error: 'Method not allowed' }, 405);

  let userId;
  try {
    ({ userId } = JSON.parse(event.body || '{}'));
  } catch {
    return respond({ error: 'Invalid JSON' }, 400);
  }
  if (!userId || typeof userId !== 'string') return respond({ error: 'userId required' }, 400);

  // Sanitise — no raw user input reaches the DB beyond parameterised queries
  userId = userId.slice(0, 256);

  const db = getPool();

  // NOTE: No try/catch here — any DB error FAILS CLOSED (returns 500, blocks the call)
  // This is intentional: a DB outage must not grant free AI access.
  let user;
  try {
    const r = await db.query(
      `SELECT id, email, is_suspended, subscription_status, subscription_plan,
              subscription_current_period_end, monthly_ai_calls, monthly_reset_at
       FROM "User"
       WHERE id::text = $1 OR email = $1
       LIMIT 1`,
      [userId]
    );
    if (!r.rows.length) return respond({ error: 'User not found' }, 404);
    user = r.rows[0];
  } catch (e) {
    console.error('[subscription-check] DB read error:', e.message);
    return respond({ allowed: false, reason: 'service_error' }, 503);
  }

  // ── Permanent whitelist ──────────────────────────────────────────────────
  if (FREE_ACCESS_EMAILS.has(user.email)) {
    return respond({ allowed: true, plan: 'premium', remaining: null });
  }

  // ── Suspended — hard block ───────────────────────────────────────────────
  if (user.is_suspended) {
    return respond({ allowed: false, reason: 'account_suspended' });
  }

  // ── Subscription validity ────────────────────────────────────────────────
  const now       = new Date();
  const status    = user.subscription_status || 'free';
  const periodEnd = user.subscription_current_period_end;
  const isPremium =
    (status === 'premium' || status === 'cancelled') &&
    periodEnd != null &&
    new Date(periodEnd) > now;

  if (!isPremium) {
    return respond({ allowed: false, reason: 'free_limit_reached' });
  }

  // ── Atomic rolling-window reset (no race condition) ──────────────────────
  // If the 30-day window has expired, reset the counter to 0 atomically.
  // Uses a conditional UPDATE so only one concurrent request wins the reset.
  try {
    await db.query(
      `UPDATE "User"
       SET monthly_ai_calls = 0,
           monthly_reset_at  = NOW() + INTERVAL '30 days'
       WHERE id = $1
         AND (monthly_reset_at IS NULL OR monthly_reset_at < NOW())`,
      [user.id]
    );
  } catch (e) {
    console.error('[subscription-check] window reset error:', e.message);
    return respond({ allowed: false, reason: 'service_error' }, 503);
  }

  // ── Atomic check-and-increment (no race condition) ───────────────────────
  // The WHERE clause enforces the quota. If the UPDATE touches 0 rows, the
  // user is already at the limit — no call is allowed and no count is wasted.
  let updatedRow;
  try {
    const inc = await db.query(
      `UPDATE "User"
       SET monthly_ai_calls = monthly_ai_calls + 1,
           ai_calls_total   = ai_calls_total   + 1
       WHERE id = $1
         AND monthly_ai_calls < $2
       RETURNING monthly_ai_calls, monthly_reset_at`,
      [user.id, PREMIUM_LIMIT]
    );
    updatedRow = inc.rows[0] || null;
  } catch (e) {
    console.error('[subscription-check] increment error:', e.message);
    return respond({ allowed: false, reason: 'service_error' }, 503);
  }

  if (!updatedRow) {
    // 0 rows updated → quota already exhausted
    const resetAt = user.monthly_reset_at
      ? new Date(user.monthly_reset_at).toISOString()
      : null;
    return respond({
      allowed  : false,
      reason   : 'monthly_limit_reached',
      resetsAt : resetAt,
      remaining: 0,
      limit    : PREMIUM_LIMIT,
    });
  }

  return respond({
    allowed  : true,
    plan     : user.subscription_plan || 'monthly',
    remaining: PREMIUM_LIMIT - updatedRow.monthly_ai_calls,
    limit    : PREMIUM_LIMIT,
  });
};
