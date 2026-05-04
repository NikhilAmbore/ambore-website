/**
 * verify-payment — confirms a Dodo Payments subscription is active and
 * updates the user's DB record. Called when a user returns from checkout
 * (dashboard?upgraded=1) or clicks "Restore access" on the paywall.
 *
 * POST { userId }
 * Returns { plan: 'premium'|'free', verified: bool, renewsAt?: string }
 *
 * This is the safety net for when the webhook is delayed or fails.
 */
const DodoPayments = require('dodopayments');
const { getPool, ok, err, preflight, verifyUser } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let userId;
  try { ({ userId } = JSON.parse(event.body || '{}')); }
  catch { return err('Invalid JSON', 400); }

  const user = await verifyUser(userId);
  if (!user) return err('Not authenticated', 401);

  const dodo = new DodoPayments({
    bearerToken: process.env.DODO_PAYMENTS_API_KEY,
    environment: process.env.DODO_ENVIRONMENT || 'live_mode',
  });

  const db = getPool();

  try {
    // Check if already premium in DB (webhook may have already fired)
    const existing = await db.query(
      `SELECT subscription_status, subscription_current_period_end, dodo_customer_id
       FROM "User" WHERE id = $1`,
      [user.id]
    );
    const row = existing.rows[0] || {};
    const now = new Date();
    const periodEnd = row.subscription_current_period_end;
    if (
      row.subscription_status === 'premium' &&
      (!periodEnd || new Date(periodEnd) > now)
    ) {
      return ok({ plan: 'premium', verified: true, source: 'db_already_set' });
    }

    // Look up Dodo customer — prefer stored ID, fall back to email lookup
    let customerId = row.dodo_customer_id || null;

    if (!customerId) {
      try {
        const custPage = await dodo.customers.list({ email: user.email });
        const customers = custPage.items || [];
        const match = customers.find(c => c.email?.toLowerCase() === user.email.toLowerCase());
        customerId = match?.customer_id || null;
      } catch (e) {
        console.warn('[verify-payment] customer lookup failed:', e.message);
      }
    }

    if (!customerId) {
      return ok({ plan: 'free', verified: false, message: 'No payment account found for this email' });
    }

    // List active subscriptions for this customer
    const productId = process.env.DODO_PRODUCT_ID;
    let activeSub = null;

    try {
      const subPage = await dodo.subscriptions.list({
        customer_id: customerId,
        status: 'active',
        ...(productId ? { product_id: productId } : {}),
      });
      const subs = subPage.items || [];
      activeSub = subs[0] || null;
    } catch (e) {
      console.warn('[verify-payment] subscription lookup failed:', e.message);
      // Try without product_id filter in case it caused an issue
      try {
        const subPage2 = await dodo.subscriptions.list({ customer_id: customerId, status: 'active' });
        activeSub = (subPage2.items || [])[0] || null;
      } catch (e2) {
        console.error('[verify-payment] fallback subscription lookup failed:', e2.message);
      }
    }

    if (!activeSub) {
      return ok({ plan: 'free', verified: false, message: 'No active subscription found' });
    }

    // Active subscription confirmed — update DB
    const subId     = activeSub.subscription_id || activeSub.id;
    const renewsAt  = activeSub.next_billing_date || null;

    await db.query(
      `UPDATE "User"
       SET subscription_status             = 'premium',
           dodo_customer_id                = COALESCE($1, dodo_customer_id),
           dodo_subscription_id            = COALESCE($2, dodo_subscription_id),
           subscription_current_period_end = COALESCE($3, subscription_current_period_end)
       WHERE id = $4`,
      [customerId, subId, renewsAt, user.id]
    );

    console.log('[verify-payment] activated premium for user', user.id, 'sub', subId);

    return ok({ plan: 'premium', verified: true, renewsAt, source: 'dodo_api' });

  } catch (e) {
    console.error('[verify-payment]', e.message);
    return err('Verification failed: ' + e.message, 500);
  }
};
