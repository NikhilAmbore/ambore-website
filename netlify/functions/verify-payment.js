/**
 * verify-payment — confirms a Dodo Payments subscription is active.
 *
 * Security fixes:
 *  1. COALESCE removed — subscription_current_period_end always written explicitly
 *     so expired subscriptions can never persist as "premium" indefinitely
 *  2. Idempotent UPDATE uses explicit value (not COALESCE fallback)
 *  3. IP rate limit: max 10 verify attempts per IP per 10 minutes
 */
const DodoPayments = require('dodopayments');
const { getPool, ok, err, preflight, verifyUser, clientIp, checkIpLimit } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return preflight();
  if (event.httpMethod !== 'POST') return err('Method not allowed', 405);

  let userId;
  try { ({ userId } = JSON.parse(event.body || '{}')); }
  catch { return err('Invalid JSON', 400); }

  const ip = clientIp(event);
  const db = getPool();

  // ── IP rate limit ──────────────────────────────────────────────────────────
  const ipBlocked = await checkIpLimit(db, ip, 'verify_payment', 10, 10);
  if (ipBlocked.blocked) return err('Too many verification attempts. Wait 10 minutes.', 429);

  const user = await verifyUser(userId);
  if (!user) return err('Not authenticated', 401);

  const dodo = new DodoPayments({
    bearerToken: process.env.DODO_PAYMENTS_API_KEY,
    environment: process.env.DODO_ENVIRONMENT || 'live_mode',
  });

  try {
    // Check if already premium in DB
    const existing = await db.query(
      `SELECT subscription_status, subscription_current_period_end, dodo_customer_id
       FROM "User" WHERE id = $1`,
      [user.id]
    );
    const row       = existing.rows[0] || {};
    const now       = new Date();
    const periodEnd = row.subscription_current_period_end;

    if (row.subscription_status === 'premium' && periodEnd && new Date(periodEnd) > now) {
      return ok({ plan: 'premium', verified: true, source: 'db_already_set' });
    }

    // Look up Dodo customer
    let customerId = row.dodo_customer_id || null;
    if (!customerId) {
      try {
        const custPage  = await dodo.customers.list({ email: user.email });
        const customers = custPage.items || [];
        const match     = customers.find(c => c.email?.toLowerCase() === user.email.toLowerCase());
        customerId = match?.customer_id || null;
      } catch (e) {
        console.warn('[verify-payment] customer lookup failed:', e.message);
      }
    }

    if (!customerId) {
      return ok({ plan: 'free', verified: false, message: 'No payment account found for this email' });
    }

    // List active subscriptions
    const productId = process.env.DODO_PRODUCT_ID_MONTHLY || process.env.DODO_PRODUCT_ID;
    let activeSub = null;
    try {
      const subPage = await dodo.subscriptions.list({ customer_id: customerId, status: 'active' });
      activeSub = (subPage.items || [])[0] || null;
    } catch (e) {
      console.warn('[verify-payment] subscription lookup failed:', e.message);
    }

    if (!activeSub) {
      return ok({ plan: 'free', verified: false, message: 'No active subscription found' });
    }

    const subId    = activeSub.subscription_id || activeSub.id;
    // Always set an explicit period end — never COALESCE from stale DB value
    const renewsAt = activeSub.next_billing_date ||
      new Date(Date.now() + 30 * 24 * 60 * 60 * 1000).toISOString();

    await db.query(
      `UPDATE "User"
       SET subscription_status             = 'premium',
           dodo_customer_id                = $1,
           dodo_subscription_id            = $2,
           subscription_current_period_end = $3
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
