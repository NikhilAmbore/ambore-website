/**
 * subscription-status — public endpoint for the client to check the logged-in
 * user's current plan and usage counters.
 *
 * GET /.netlify/functions/subscription-status?userId=<id>
 * Returns JSON:
 * {
 *   plan           : 'free' | 'premium',
 *   freeUsed       : number,
 *   freeRemaining  : number | null,
 *   monthlyUsed    : number | null,
 *   monthlyLimit   : number | null,
 *   monthlyRemaining: number | null,
 *   resetsAt       : ISO string | null,
 *   expiresAt      : ISO string | null,
 * }
 */
const { getPool, ok, err, preflight, verifyUser } = require('./_db');

const FREE_LIMIT    = 0;
const PREMIUM_LIMIT = 100;

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'GET')    return err('Method not allowed', 405);

  const userId = event.queryStringParameters?.userId;
  const user   = await verifyUser(userId);
  if (!user) return err('Not authenticated', 401);

  const db = getPool();
  try {
    const r = await db.query(
      `SELECT subscription_status, subscription_current_period_end,
              monthly_ai_calls, monthly_reset_at, ai_calls_total
       FROM "User" WHERE id = $1`,
      [user.id]
    );

    const row       = r.rows[0] || {};
    const now       = new Date();
    const status    = row.subscription_status || 'free';
    const periodEnd = row.subscription_current_period_end;
    const isPremium = status === 'premium' && (!periodEnd || new Date(periodEnd) > now);

    const used    = row.ai_calls_total    || 0;
    const monthly = row.monthly_ai_calls  || 0;
    const resetAt = row.monthly_reset_at  ? new Date(row.monthly_reset_at).toISOString() : null;

    if (isPremium) {
      return ok({
        plan             : 'premium',
        freeUsed         : used,
        freeRemaining    : null,
        monthlyUsed      : monthly,
        monthlyLimit     : PREMIUM_LIMIT,
        monthlyRemaining : Math.max(0, PREMIUM_LIMIT - monthly),
        resetsAt         : resetAt,
        expiresAt        : periodEnd ? new Date(periodEnd).toISOString() : null,
      });
    }

    return ok({
      plan             : 'free',
      freeUsed         : used,
      freeRemaining    : Math.max(0, FREE_LIMIT - used),
      monthlyUsed      : null,
      monthlyLimit     : null,
      monthlyRemaining : null,
      resetsAt         : null,
      expiresAt        : null,
    });

  } catch (e) {
    console.error('[subscription-status]', e.message);
    return err('Server error', 500);
  }
};
