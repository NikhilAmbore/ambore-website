/**
 * dodo-webhook — receives and processes Dodo Payments webhook events.
 *
 * Events handled:
 *   subscription.active    → set premium (new activation)
 *   subscription.renewed   → set premium (renewal, update period end)
 *   subscription.updated   → sync status changes
 *   subscription.cancelled → mark cancelled (stays premium until period end)
 *   subscription.on_hold   → mark on_hold (treat as non-premium)
 *   subscription.expired   → revert to free
 *   payment.succeeded      → one-time sanity log
 *
 * Register this URL in the Dodo dashboard:
 *   https://ambore.org/.netlify/functions/dodo-webhook
 */
const DodoPayments = require('dodopayments');
const { getPool } = require('./_db');

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') {
    return { statusCode: 204, body: '' };
  }
  if (event.httpMethod !== 'POST') {
    return { statusCode: 405, body: 'Method not allowed' };
  }

  // ── Signature verification ────────────────────────────────────────────────
  const dodo = new DodoPayments({
    bearerToken : process.env.DODO_PAYMENTS_API_KEY,
    environment : process.env.DODO_ENVIRONMENT || 'live_mode',
    webhookKey  : process.env.DODO_PAYMENTS_WEBHOOK_KEY,
  });

  let webhookEvent;
  try {
    webhookEvent = dodo.webhooks.unwrap(event.body, {
      headers : event.headers,
      key     : process.env.DODO_PAYMENTS_WEBHOOK_KEY,
    });
  } catch (e) {
    console.error('[dodo-webhook] Signature verification failed:', e.message);
    return { statusCode: 400, body: 'Invalid webhook signature' };
  }

  const db       = getPool();
  const evtType  = webhookEvent.type;
  const data     = webhookEvent.data || {};

  console.log('[dodo-webhook] event:', evtType, JSON.stringify(data).slice(0, 200));

  // ── Helpers ───────────────────────────────────────────────────────────────
  async function findUserId(sub) {
    // Prefer metadata.user_id set at checkout creation
    const metaUserId = sub.metadata?.user_id || sub.metadata?.userId;
    if (metaUserId) {
      const r = await db.query('SELECT id FROM "User" WHERE id = $1 LIMIT 1', [metaUserId]);
      if (r.rows.length) return r.rows[0].id;
    }
    // Fall back to dodo_customer_id
    const custId = sub.customer?.customer_id || sub.customer_id;
    if (custId) {
      const r = await db.query('SELECT id FROM "User" WHERE dodo_customer_id = $1 LIMIT 1', [custId]);
      if (r.rows.length) return r.rows[0].id;
    }
    // Fall back to email
    const email = sub.customer?.email;
    if (email) {
      const r = await db.query('SELECT id FROM "User" WHERE email = $1 LIMIT 1', [email.toLowerCase()]);
      if (r.rows.length) return r.rows[0].id;
    }
    return null;
  }

  async function setPremium(sub) {
    const userId = await findUserId(sub);
    if (!userId) { console.warn('[dodo-webhook] could not find user for sub', JSON.stringify(sub).slice(0,200)); return; }

    const subId     = sub.subscription_id || sub.id;
    const custId    = sub.customer?.customer_id || sub.customer_id;
    const periodEnd = sub.next_billing_date || null;

    await db.query(
      `UPDATE "User"
       SET subscription_status              = 'premium',
           dodo_subscription_id             = $1,
           dodo_customer_id                 = COALESCE($2, dodo_customer_id),
           subscription_current_period_end  = $3
       WHERE id = $4`,
      [subId, custId || null, periodEnd, userId]
    );
    console.log('[dodo-webhook] set premium for user', userId);
  }

  async function setStatus(sub, status) {
    const userId = await findUserId(sub);
    if (!userId) return;

    const periodEnd = sub.next_billing_date || null;

    await db.query(
      `UPDATE "User"
       SET subscription_status             = $1,
           subscription_current_period_end = COALESCE($2, subscription_current_period_end)
       WHERE id = $3`,
      [status, periodEnd, userId]
    );
    console.log('[dodo-webhook] set status', status, 'for user', userId);
  }

  // ── Event routing ─────────────────────────────────────────────────────────
  try {
    switch (evtType) {
      case 'subscription.active':
      case 'subscription.renewed':
        await setPremium(data);
        break;

      case 'subscription.updated':
        // Reflect status accurately — could be active or paused etc.
        if (data.status === 'active') {
          await setPremium(data);
        } else {
          await setStatus(data, data.status || 'updated');
        }
        break;

      case 'subscription.cancelled':
        // Keep period end so user retains access until billing date
        await setStatus(data, 'cancelled');
        break;

      case 'subscription.on_hold':
        await setStatus(data, 'on_hold');
        break;

      case 'subscription.expired':
        await setStatus(data, 'free');
        break;

      default:
        // Unhandled events are OK — just acknowledge
        break;
    }
  } catch (e) {
    console.error('[dodo-webhook] DB update failed:', e.message);
    // Still return 200 so Dodo doesn't retry indefinitely
  }

  return { statusCode: 200, body: JSON.stringify({ received: true }) };
};
