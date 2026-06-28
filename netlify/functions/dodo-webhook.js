/**
 * dodo-webhook — receives and processes Dodo Payments webhook events.
 *
 * Events handled:
 *   subscription.active    → set premium + store plan type
 *   subscription.renewed   → refresh period end
 *   subscription.updated   → sync status changes
 *   subscription.cancelled → mark cancelled (stays premium until period end)
 *   subscription.on_hold   → mark on_hold (non-premium)
 *   subscription.expired   → revert to free
 *
 *   dispute.created              → SUSPEND account immediately (chargeback protection)
 *   payment.dispute.created      → same (alias sent by some Dodo SDK versions)
 *   payment.dispute.won          → keep suspended (dispute resolved in our favour)
 *   payment.dispute.lost         → keep suspended (bank ruled for customer)
 *   payment.dispute.needs_response → log; no action (awaiting our evidence)
 *
 * Plan detection via metadata.plan set at checkout creation:
 *   monthly | 3month | 6month | 1year
 *
 * Register this URL in the Dodo dashboard:
 *   https://offerly.org/.netlify/functions/dodo-webhook
 */
const DodoPayments = require('dodopayments');
const { getPool } = require('./_db');

const VALID_PLANS = new Set(['monthly', '3month', '6month', '1year']);

function resolvePlan(meta) {
  const p = meta?.plan || meta?.subscription_plan;
  return VALID_PLANS.has(p) ? p : 'monthly';
}

exports.handler = async (event) => {
  if (event.httpMethod === 'OPTIONS') return { statusCode: 204, body: '' };
  if (event.httpMethod !== 'POST')   return { statusCode: 405, body: 'Method not allowed' };

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

  const db      = getPool();
  const evtType = webhookEvent.type;
  const data    = webhookEvent.data || {};

  console.log('[dodo-webhook] event:', evtType, JSON.stringify(data).slice(0, 200));

  // ── Helpers ───────────────────────────────────────────────────────────────
  async function findUserId(sub) {
    const metaUserId = sub.metadata?.user_id || sub.metadata?.userId;
    if (metaUserId) {
      const r = await db.query('SELECT id FROM "User" WHERE id = $1 LIMIT 1', [metaUserId]);
      if (r.rows.length) return r.rows[0].id;
    }
    const custId = sub.customer?.customer_id || sub.customer_id;
    if (custId) {
      const r = await db.query('SELECT id FROM "User" WHERE dodo_customer_id = $1 LIMIT 1', [custId]);
      if (r.rows.length) return r.rows[0].id;
    }
    const email = sub.customer?.email;
    if (email) {
      const r = await db.query('SELECT id FROM "User" WHERE email = $1 LIMIT 1', [email.toLowerCase()]);
      if (r.rows.length) return r.rows[0].id;
    }
    return null;
  }

  async function setPremium(sub) {
    const userId = await findUserId(sub);
    if (!userId) {
      console.warn('[dodo-webhook] could not find user for sub', JSON.stringify(sub).slice(0, 200));
      return;
    }

    const subId     = sub.subscription_id || sub.id;
    const custId    = sub.customer?.customer_id || sub.customer_id;
    const periodEnd = sub.next_billing_date || null;
    const plan      = resolvePlan(sub.metadata);

    await db.query(
      `UPDATE "User"
       SET subscription_status             = 'premium',
           subscription_plan               = $1,
           dodo_subscription_id            = $2,
           dodo_customer_id                = COALESCE($3, dodo_customer_id),
           subscription_current_period_end = $4
       WHERE id = $5`,
      [plan, subId, custId || null, periodEnd, userId]
    );
    console.log('[dodo-webhook] set premium (plan=%s) for user %s', plan, userId);
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
    console.log('[dodo-webhook] set status=%s for user %s', status, userId);
  }

  // Suspend account due to payment dispute — called immediately on dispute.created.
  // The account stays suspended regardless of outcome so the user cannot keep
  // consuming AI credits while a chargeback is in flight.
  async function suspendForDispute(data) {
    // Dispute events may embed payment/subscription or customer data directly.
    // Try every known field path so we find the user regardless of SDK version.
    const candidate = {
      metadata   : data.metadata || data.payment?.metadata || data.subscription?.metadata,
      customer   : data.customer || data.payment?.customer || {},
      customer_id: data.customer_id || data.payment?.customer_id
                    || data.customer?.customer_id,
    };

    const userId = await findUserId(candidate);
    if (!userId) {
      console.warn('[dodo-webhook] dispute: could not resolve user from event — raw:',
        JSON.stringify(data).slice(0, 300));
      return;
    }

    await db.query(
      `UPDATE "User" SET is_suspended = true WHERE id = $1`,
      [userId]
    );

    // Log the dispute in ActivityLog for audit trail / evidence export
    const disputeId  = data.dispute_id || data.id || 'unknown';
    const amount     = data.amount ?? data.payment?.amount ?? null;
    const currency   = data.currency || data.payment?.currency || 'USD';
    const reason     = data.reason || data.dispute_reason || 'unknown';
    try {
      await db.query(
        `INSERT INTO "ActivityLog" (id, "userId", type, metadata, "createdAt")
         VALUES (gen_random_uuid()::text, $1, 'payment_dispute', $2, NOW())`,
        [userId, JSON.stringify({ disputeId, amount, currency, reason, evtType })]
      );
    } catch (logErr) {
      console.error('[dodo-webhook] dispute log insert failed:', logErr.message);
    }

    console.error('[dodo-webhook] DISPUTE FILED — suspended user %s | disputeId=%s amount=%s %s reason=%s',
      userId, disputeId, amount, currency, reason);
  }

  // ── Event routing ─────────────────────────────────────────────────────────
  try {
    switch (evtType) {
      case 'subscription.active':
      case 'subscription.renewed':
        await setPremium(data);
        break;

      case 'subscription.updated':
        if (data.status === 'active') {
          await setPremium(data);
        } else {
          await setStatus(data, data.status || 'updated');
        }
        break;

      case 'subscription.cancelled':
        await setStatus(data, 'cancelled');
        break;

      case 'subscription.on_hold':
        await setStatus(data, 'on_hold');
        break;

      case 'subscription.expired':
        await setStatus(data, 'free');
        break;

      // ── Dispute / chargeback events ─────────────────────────────────────
      case 'dispute.created':
      case 'payment.dispute.created':
        await suspendForDispute(data);
        break;

      // Dispute resolved in merchant's favour — account stays suspended;
      // manual review needed before reinstating.
      case 'dispute.won':
      case 'payment.dispute.won':
        console.log('[dodo-webhook] dispute WON for event', JSON.stringify(data).slice(0, 200));
        break;

      // Bank ruled for customer — account already suspended, nothing more to do.
      case 'dispute.lost':
      case 'payment.dispute.lost':
        console.warn('[dodo-webhook] dispute LOST for event', JSON.stringify(data).slice(0, 200));
        break;

      case 'payment.dispute.needs_response':
        console.warn('[dodo-webhook] dispute NEEDS RESPONSE:', JSON.stringify(data).slice(0, 300));
        break;

      default:
        // Log all unhandled events so we can identify the correct dispute event
        // name the first time Dodo fires one in production.
        console.log('[dodo-webhook] unhandled event type:', evtType,
          JSON.stringify(data).slice(0, 200));
        break;
    }
  } catch (e) {
    console.error('[dodo-webhook] DB update failed:', e.message);
    // Return 200 so Dodo does not retry indefinitely
  }

  return { statusCode: 200, body: JSON.stringify({ received: true }) };
};
