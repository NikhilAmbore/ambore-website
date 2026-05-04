/**
 * create-checkout — creates a Dodo Payments hosted checkout session.
 * POST { userId }  →  JSON { url }  (redirect the browser to url)
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
    bearerToken : process.env.DODO_PAYMENTS_API_KEY,
    environment : process.env.DODO_ENVIRONMENT || 'live_mode',
  });

  const db      = getPool();
  const siteUrl = process.env.URL || 'https://ambore.org';

  try {
    // Retrieve existing Dodo customer ID if we have one
    const r = await db.query(
      'SELECT dodo_customer_id, subscription_status, subscription_current_period_end FROM "User" WHERE id = $1',
      [user.id]
    );
    const row = r.rows[0] || {};

    // Don't let an already-active premium user create another session
    const periodEnd = row.subscription_current_period_end;
    if (
      row.subscription_status === 'premium' &&
      (!periodEnd || new Date(periodEnd) > new Date())
    ) {
      return err('Already subscribed to Premium.', 409);
    }

    // Build checkout session
    // Note: dodo_customer_id is stored via the subscription.active webhook event.
    // metadata.user_id links the subscription back to our user record.
    const session = await dodo.checkoutSessions.create({
      product_cart : [{ product_id: process.env.DODO_PRODUCT_ID, quantity: 1 }],
      customer     : { email: user.email, name: user.name || user.email },
      return_url   : `${siteUrl}/dashboard?upgraded=1`,
      metadata     : { user_id: String(user.id) },
    });

    const checkoutUrl = session.checkout_url || session.url;
    if (!checkoutUrl) return err('Failed to create checkout session', 502);

    return ok({ url: checkoutUrl });

  } catch (e) {
    console.error('[create-checkout]', e.message);
    return err('Payment service error: ' + e.message, 502);
  }
};
