/**
 * create-checkout — creates a Dodo Payments hosted checkout session.
 *
 * POST { userId, plan }
 *   plan: 'monthly' | '3month' | '6month' | '1year'  (defaults to 'monthly')
 *
 * Required env vars (set one product ID per plan in Dodo dashboard):
 *   DODO_PRODUCT_ID_MONTHLY
 *   DODO_PRODUCT_ID_3MONTH
 *   DODO_PRODUCT_ID_6MONTH
 *   DODO_PRODUCT_ID_1YEAR
 *   DODO_PRODUCT_ID  (legacy fallback → monthly)
 *
 * Returns JSON { url }  — redirect the browser to url.
 */
const DodoPayments = require('dodopayments');
const { getPool, ok, err, preflight, verifyUser } = require('./_db');

const VALID_PLANS = new Set(['monthly', '3month', '6month', '1year']);

function productIdForPlan(plan) {
  switch (plan) {
    case '3month': return process.env.DODO_PRODUCT_ID_3MONTH;
    case '6month': return process.env.DODO_PRODUCT_ID_6MONTH;
    case '1year':  return process.env.DODO_PRODUCT_ID_1YEAR;
    default:       return process.env.DODO_PRODUCT_ID_MONTHLY || process.env.DODO_PRODUCT_ID;
  }
}

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let userId, plan;
  try {
    ({ userId, plan } = JSON.parse(event.body || '{}'));
  } catch {
    return err('Invalid JSON', 400);
  }

  // Default to monthly; reject unknown plan names
  plan = plan || 'monthly';
  if (!VALID_PLANS.has(plan)) return err(`Invalid plan. Choose: ${[...VALID_PLANS].join(', ')}`, 400);

  const user = await verifyUser(userId);
  if (!user) return err('Not authenticated', 401);

  const productId = productIdForPlan(plan);
  if (!productId) return err(`Product not configured for plan: ${plan}`, 503);

  const dodo = new DodoPayments({
    bearerToken : process.env.DODO_PAYMENTS_API_KEY,
    environment : process.env.DODO_ENVIRONMENT || 'live_mode',
  });

  const db      = getPool();
  const siteUrl = process.env.URL || 'https://astraoffer.org';

  try {
    const r = await db.query(
      `SELECT dodo_customer_id, subscription_status, subscription_current_period_end,
              is_suspended
       FROM "User" WHERE id = $1`,
      [user.id]
    );
    const row = r.rows[0] || {};

    // Block suspended accounts
    if (row.is_suspended) return err('Account suspended. Contact support@astraoffer.org.', 403);

    // Block if already on an active Premium subscription
    const periodEnd = row.subscription_current_period_end;
    if (
      (row.subscription_status === 'premium' || row.subscription_status === 'cancelled') &&
      periodEnd && new Date(periodEnd) > new Date()
    ) {
      return err('You already have an active Premium subscription.', 409);
    }

    const session = await dodo.checkoutSessions.create({
      product_cart : [{ product_id: productId, quantity: 1 }],
      customer     : { email: user.email, name: user.name || user.email },
      return_url   : `${siteUrl}/dashboard?upgraded=1&plan=${plan}`,
      metadata     : { user_id: String(user.id), plan },
    });

    const checkoutUrl = session.checkout_url || session.url;
    if (!checkoutUrl) return err('Failed to create checkout session', 502);

    return ok({ url: checkoutUrl });

  } catch (e) {
    console.error('[create-checkout]', e.message);
    return err('Payment service error: ' + e.message, 502);
  }
};
