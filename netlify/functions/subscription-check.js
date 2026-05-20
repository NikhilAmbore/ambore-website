/**
 * subscription-check — internal endpoint called by the claude-proxy edge function.
 * Checks whether the user is allowed to make an AI call, then atomically
 * increments their usage counter if allowed.
 *
 * Free tier  : 0 AI calls — Premium required.
 * Premium    : 1,000 AI calls per rolling 30-day period.
 * Plans      : monthly ($29) | 3month ($75) | 6month ($139) | 1year ($249)
 *
 * Strict rules enforced:
 *  - Suspended accounts are hard-blocked.
 *  - Expired subscriptions are hard-blocked regardless of status field.
 *  - Monthly call quota is per rolling 30-day window, not per calendar month.
 *
 * Called with POST { userId } — returns JSON { allowed, reason?, remaining? }
 */
const { getPool, preflight } = require('./_db');

const FREE_LIMIT    = 0;
const PREMIUM_LIMIT = 1000; // AI calls per rolling 30-day window

// Permanent free Premium access (owner / internal)
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
  if (!userId) return respond({ error: 'userId required' }, 400);

  const db = getPool();

  try {
    const r = await db.query(
      `SELECT id, email, is_suspended, subscription_status, subscription_plan,
              subscription_current_period_end, monthly_ai_calls, monthly_reset_at,
              ai_calls_total
       FROM "User"
       WHERE id::text = $1 OR email = $1
       LIMIT 1`,
      [userId]
    );

    if (!r.rows.length) return respond({ error: 'User not found' }, 404);
    const user = r.rows[0];

    // ── Permanent free access whitelist ──────────────────────────────────────
    if (FREE_ACCESS_EMAILS.has(user.email)) {
      return respond({ allowed: true, plan: 'premium', remaining: null });
    }

    // ── Hard block suspended accounts ────────────────────────────────────────
    if (user.is_suspended) {
      return respond({
        allowed : false,
        reason  : 'account_suspended',
        message : 'Your account has been suspended. Contact support@ambore.org.',
      });
    }

    const now       = new Date();
    const status    = user.subscription_status || 'free';
    const periodEnd = user.subscription_current_period_end;

    // Premium = status is 'premium' OR 'cancelled' (still within paid period)
    const activePremium =
      (status === 'premium' || status === 'cancelled') &&
      periodEnd &&
      new Date(periodEnd) > now;

    if (activePremium) {
      // ── Rolling 30-day window ─────────────────────────────────────────────
      let monthlyCalls = user.monthly_ai_calls || 0;
      let resetAt      = user.monthly_reset_at ? new Date(user.monthly_reset_at) : null;

      if (!resetAt || now > resetAt) {
        monthlyCalls = 0;
        resetAt      = new Date(now.getTime() + 30 * 24 * 60 * 60 * 1000);
        await db.query(
          `UPDATE "User" SET monthly_ai_calls = 0, monthly_reset_at = $1 WHERE id = $2`,
          [resetAt.toISOString(), user.id]
        );
      }

      if (monthlyCalls >= PREMIUM_LIMIT) {
        return respond({
          allowed  : false,
          reason   : 'monthly_limit_reached',
          resetsAt : resetAt.toISOString(),
          remaining: 0,
          limit    : PREMIUM_LIMIT,
        });
      }

      await db.query(
        `UPDATE "User"
         SET monthly_ai_calls = monthly_ai_calls + 1,
             ai_calls_total   = ai_calls_total   + 1
         WHERE id = $1`,
        [user.id]
      );

      return respond({
        allowed  : true,
        plan     : user.subscription_plan || 'monthly',
        remaining: PREMIUM_LIMIT - monthlyCalls - 1,
        limit    : PREMIUM_LIMIT,
      });
    }

    // ── Free tier — 0 calls allowed ───────────────────────────────────────────
    return respond({
      allowed: false,
      reason : 'free_limit_reached',
      message: 'Upgrade to Premium to use AI tools.',
    });

  } catch (e) {
    console.error('[subscription-check]', e.message);
    // Fail open so a DB hiccup doesn't break all AI calls
    return respond({ allowed: true, plan: 'unknown', remaining: null });
  }
};
