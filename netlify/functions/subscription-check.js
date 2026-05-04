/**
 * subscription-check — internal endpoint called by the claude-proxy edge function.
 * Checks whether the user is allowed to make an AI call, then atomically
 * increments their usage counter if allowed.
 *
 * Free tier  : 1 lifetime AI call per account.
 * Premium    : 100 AI calls per rolling 30-day period for $9/month.
 *
 * Called with POST { userId } — returns JSON { allowed, reason?, remaining? }
 */
const { getPool, preflight } = require('./_db');

const FREE_LIMIT    = 1;
const PREMIUM_LIMIT = 100;

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
  if (!userId) return respond({ error: 'userId required' }, 400);

  const db = getPool();

  try {
    const r = await db.query(
      `SELECT id, subscription_status, subscription_current_period_end,
              monthly_ai_calls, monthly_reset_at, ai_calls_total
       FROM "User"
       WHERE id::text = $1 OR email = $1
       LIMIT 1`,
      [userId]
    );

    if (!r.rows.length) return respond({ error: 'User not found' }, 404);
    const user = r.rows[0];

    const now        = new Date();
    const status     = user.subscription_status || 'free';
    const periodEnd  = user.subscription_current_period_end;
    const isPremium  = status === 'premium' && (!periodEnd || new Date(periodEnd) > now);

    if (isPremium) {
      // ── Premium: rolling 30-day window ───────────────────────────────────────
      let monthlyCalls = user.monthly_ai_calls || 0;
      let resetAt      = user.monthly_reset_at ? new Date(user.monthly_reset_at) : null;

      if (!resetAt || now > resetAt) {
        // Window expired — reset counter
        monthlyCalls = 0;
        resetAt      = new Date(now.getTime() + 30 * 24 * 60 * 60 * 1000);
        await db.query(
          `UPDATE "User" SET monthly_ai_calls = 0, monthly_reset_at = $1
           WHERE id = $2`,
          [resetAt.toISOString(), user.id]
        );
      }

      if (monthlyCalls >= PREMIUM_LIMIT) {
        return respond({
          allowed   : false,
          reason    : 'monthly_limit_reached',
          resetsAt  : resetAt.toISOString(),
          remaining : 0,
        });
      }

      // Increment both counters atomically
      await db.query(
        `UPDATE "User"
         SET monthly_ai_calls = monthly_ai_calls + 1,
             ai_calls_total   = ai_calls_total   + 1
         WHERE id = $1`,
        [user.id]
      );

      return respond({
        allowed   : true,
        plan      : 'premium',
        remaining : PREMIUM_LIMIT - monthlyCalls - 1,
      });
    }

    // ── Free tier ─────────────────────────────────────────────────────────────
    const used = user.ai_calls_total || 0;

    if (used >= FREE_LIMIT) {
      return respond({
        allowed : false,
        reason  : 'free_limit_reached',
        used,
      });
    }

    await db.query(
      `UPDATE "User" SET ai_calls_total = ai_calls_total + 1 WHERE id = $1`,
      [user.id]
    );

    return respond({
      allowed   : true,
      plan      : 'free',
      remaining : FREE_LIMIT - used - 1,
    });

  } catch (e) {
    console.error('[subscription-check]', e.message);
    // Fail open so a DB hiccup doesn't break all AI calls
    return respond({ allowed: true, plan: 'unknown', remaining: null });
  }
};
