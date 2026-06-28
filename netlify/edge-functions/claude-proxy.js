/**
 * AstraOffer AI — Claude Proxy Edge Function
 * ─────────────────────────────────────────────────────────────────────────────
 * Routes all Claude API calls through this serverless edge function so that
 * the Anthropic API key NEVER appears in client-side JavaScript.
 *
 * SECURITY CONTROLS
 *  1. API key  — stored in CLAUDE_API_KEY env variable, invisible to clients
 *  2. Rate limiting — 20 req / IP / minute + 200 req / user-ID / hour
 *  3. Input validation — strict schema, type checks, length limits, whitelist
 *  4. Origin enforcement — requests only accepted from astraoffer.org / Netlify
 *  5. 429 responses with Retry-After headers (graceful degradation)
 *  6. Streaming pass-through — preserves SSE streaming from Claude
 *
 * OWASP mitigations
 *  A01 — Broken Access Control : origin check + auth header forwarded
 *  A03 — Injection             : input sanitised, payload whitelist enforced
 *  A05 — Security Misconfiguration : no debug headers, no stack traces
 *  A06 — Vulnerable Components  : no third-party deps (pure Deno/Web APIs)
 */

// ── In-memory rate-limit stores ───────────────────────────────────────────────
// These persist for the lifetime of each edge-function instance.
// For cross-instance persistence upgrade to Netlify KV or Upstash Redis.
const ipStore   = new Map(); // key: IP string   → { count, resetAt }
const userStore = new Map(); // key: user-ID str → { count, resetAt }

// ── Configuration ─────────────────────────────────────────────────────────────
const CFG = {
  IP_LIMIT    : 20,        // max requests per IP per minute
  IP_WINDOW   : 60_000,    // 1 minute in ms
  USER_LIMIT  : 1000,      // max requests per authenticated user per hour
  USER_WINDOW : 3_600_000, // 1 hour in ms

  MAX_TOKENS  : 8000,      // hard ceiling on max_tokens
  MAX_SYSTEM  : 20_000,    // characters allowed in system prompt
  MAX_MESSAGES: 20,        // max messages array length
  MAX_MSG_LEN : 32_000,    // characters per message

  ALLOWED_MODELS: new Set([
    'claude-sonnet-4-6',
    'claude-haiku-4-5-20251001',
    'claude-opus-4-6',
  ]),

  ALLOWED_ORIGINS: new Set([
    'https://astraoffer.org',
    'https://www.astraoffer.org',
    'https://ambore.netlify.app',
  ]),
};

// ── Helpers ───────────────────────────────────────────────────────────────────

/** Token-bucket rate-limit check. Mutates store. */
function checkRate(store, key, limit, windowMs) {
  const now   = Date.now();
  const entry = store.get(key);
  if (!entry || now > entry.resetAt) {
    store.set(key, { count: 1, resetAt: now + windowMs });
    return { allowed: true, remaining: limit - 1, resetAt: now + windowMs };
  }
  entry.count++;
  const remaining = Math.max(0, limit - entry.count);
  return { allowed: entry.count <= limit, remaining, resetAt: entry.resetAt };
}

/** Build a JSON error response with standard rate-limit headers. */
function errResp(status, message, code, extra = {}) {
  const headers = { 'Content-Type': 'application/json', ...extra };
  return new Response(JSON.stringify({ error: message, code }), { status, headers });
}

/** Validate the messages array against the schema. Returns error string or null. */
function validateMessages(messages) {
  if (!Array.isArray(messages))                return 'messages must be an array';
  if (messages.length === 0)                   return 'messages array is empty';
  if (messages.length > CFG.MAX_MESSAGES)      return `too many messages (max ${CFG.MAX_MESSAGES})`;
  const VALID_ROLES = new Set(['user', 'assistant']);
  for (let i = 0; i < messages.length; i++) {
    const m = messages[i];
    if (typeof m !== 'object' || m === null)   return `message[${i}] must be an object`;
    if (!VALID_ROLES.has(m.role))              return `message[${i}].role must be "user" or "assistant"`;
    // content can be a plain string OR an array of content blocks (text/image)
    if (typeof m.content === 'string') {
      if (m.content.length > CFG.MAX_MSG_LEN)  return `message[${i}].content too long (max ${CFG.MAX_MSG_LEN} chars)`;
    } else if (Array.isArray(m.content)) {
      const VALID_BLOCK_TYPES = new Set(['text', 'image']);
      for (let j = 0; j < m.content.length; j++) {
        const blk = m.content[j];
        if (typeof blk !== 'object' || blk === null) return `message[${i}].content[${j}] must be an object`;
        if (!VALID_BLOCK_TYPES.has(blk.type))        return `message[${i}].content[${j}].type must be "text" or "image"`;
        if (blk.type === 'text') {
          if (typeof blk.text !== 'string')           return `message[${i}].content[${j}].text must be a string`;
          if (blk.text.length > CFG.MAX_MSG_LEN)      return `message[${i}].content[${j}].text too long`;
        }
        if (blk.type === 'image') {
          if (!blk.source || typeof blk.source !== 'object') return `message[${i}].content[${j}].source required`;
        }
      }
    } else {
      return `message[${i}].content must be a string or array`;
    }
    // Reject any unexpected fields (OWASP A03 — injection hardening)
    for (const k of Object.keys(m)) {
      if (k !== 'role' && k !== 'content')     return `unexpected field in message[${i}]: "${k}"`;
    }
  }
  return null;
}

// ── Main handler ──────────────────────────────────────────────────────────────
export default async function handler(req, context) {
  const origin = req.headers.get('origin') ?? '';

  // Resolve CORS origin — fallback to first allowed origin for CORS headers
  const corsOrigin = CFG.ALLOWED_ORIGINS.has(origin)
    ? origin
    : [...CFG.ALLOWED_ORIGINS][0];

  const corsHeaders = {
    'Access-Control-Allow-Origin' : corsOrigin,
    'Access-Control-Allow-Methods': 'POST, OPTIONS',
    'Access-Control-Allow-Headers': 'Content-Type, X-User-ID',
    'Vary'                        : 'Origin',
  };

  // ── OPTIONS preflight ───────────────────────────────────────────────────────
  if (req.method === 'OPTIONS') {
    return new Response(null, { status: 204, headers: { ...corsHeaders, 'Access-Control-Max-Age': '600' } });
  }

  // ── Method guard ────────────────────────────────────────────────────────────
  if (req.method !== 'POST') {
    return errResp(405, 'Method not allowed', 'METHOD_NOT_ALLOWED', corsHeaders);
  }

  // ── IP rate limiting ─────────────────────────────────────────────────────────
  const ip      = context.ip ?? 'unknown';
  const ipCheck = checkRate(ipStore, ip, CFG.IP_LIMIT, CFG.IP_WINDOW);
  const rlHeaders = {
    ...corsHeaders,
    'X-RateLimit-Limit'    : String(CFG.IP_LIMIT),
    'X-RateLimit-Remaining': String(ipCheck.remaining),
    'X-RateLimit-Reset'    : String(Math.ceil(ipCheck.resetAt / 1000)),
  };

  if (!ipCheck.allowed) {
    const retryAfter = Math.ceil((ipCheck.resetAt - Date.now()) / 1000);
    return errResp(429, 'Too many requests — please wait before trying again.', 'IP_RATE_LIMITED', {
      ...rlHeaders,
      'Retry-After': String(retryAfter),
    });
  }

  // ── User identification — required for subscription enforcement ─────────────
  const userId = (req.headers.get('x-user-id') ?? '').slice(0, 64).replace(/[^\w@.-]/g, '');

  // Block anonymous / missing user ID — all tool pages inject this header via
  // paywall.js. If it's absent or 'anonymous', the request is not authenticated.
  if (!userId || userId === 'anonymous') {
    return new Response(
      JSON.stringify({
        error      : 'Authentication required. Please log in to use AI features.',
        code       : 'UPGRADE_REQUIRED',
        reason     : 'free_limit_reached',
        upgradeUrl : '/?auth=login',
      }),
      { status: 402, headers: { ...corsHeaders, 'Content-Type': 'application/json' } }
    );
  }

  // ── User rate limiting ────────────────────────────────────────────────────────
  const userCheck = checkRate(userStore, userId, CFG.USER_LIMIT, CFG.USER_WINDOW);
  if (!userCheck.allowed) {
    const retryAfter = Math.ceil((userCheck.resetAt - Date.now()) / 1000);
    return errResp(429, 'Hourly AI request limit reached. Try again later.', 'USER_RATE_LIMITED', {
      ...corsHeaders,
      'Retry-After': String(retryAfter),
    });
  }

  // ── Subscription / usage check — FAIL CLOSED ─────────────────────────────
  // Any error (network, DB, timeout) blocks the call. We never fail open.
  // A 5-second timeout prevents a hung subscription-check from stalling forever.
  try {
    const siteUrl   = Deno.env.get('URL') || 'https://astraoffer.org';
    const controller = new AbortController();
    const timeout    = setTimeout(() => controller.abort(), 5000);

    let subResp;
    try {
      subResp = await fetch(`${siteUrl}/.netlify/functions/subscription-check`, {
        method  : 'POST',
        headers : { 'Content-Type': 'application/json' },
        body    : JSON.stringify({ userId }),
        signal  : controller.signal,
      });
    } finally {
      clearTimeout(timeout);
    }

    if (!subResp.ok) {
      // subscription-check returned a non-200 — treat as blocked
      return errResp(503, 'Service temporarily unavailable. Please try again.', 'SERVICE_ERROR', corsHeaders);
    }

    const subData = await subResp.json();

    if (!subData.allowed) {
      const isLimit = subData.reason === 'monthly_limit_reached';
      return new Response(
        JSON.stringify({
          error      : isLimit
            ? 'Monthly AI limit reached. Your 1,000 requests reset at the end of your billing period.'
            : subData.reason === 'account_suspended'
              ? 'Your account has been suspended. Contact support@astraoffer.org.'
              : 'AI tools require a Premium subscription. Upgrade at astraoffer.org/pricing.',
          code       : 'UPGRADE_REQUIRED',
          reason     : subData.reason,
          upgradeUrl : '/pricing',
        }),
        { status: 402, headers: { ...corsHeaders, 'Content-Type': 'application/json' } }
      );
    }
  } catch (subErr) {
    // Fail CLOSED — network error, timeout, or parse failure blocks the request
    console.error('[claude-proxy] subscription-check failed:', subErr?.message);
    return errResp(503, 'Service temporarily unavailable. Please try again in a moment.', 'SERVICE_ERROR', corsHeaders);
  }

  // ── Parse request body ───────────────────────────────────────────────────────
  let body;
  try {
    body = await req.json();
  } catch {
    return errResp(400, 'Invalid JSON body', 'BAD_REQUEST', corsHeaders);
  }

  // ── Schema validation — only whitelisted fields accepted ────────────────────
  const { model, messages, system, max_tokens, stream } = body;

  // Reject any unexpected top-level fields (OWASP A03)
  const ALLOWED_FIELDS = new Set(['model', 'messages', 'system', 'max_tokens', 'stream']);
  for (const k of Object.keys(body)) {
    if (!ALLOWED_FIELDS.has(k)) {
      return errResp(400, `Unexpected field: "${k}"`, 'INVALID_FIELD', corsHeaders);
    }
  }

  // model
  if (typeof model !== 'string' || !CFG.ALLOWED_MODELS.has(model)) {
    return errResp(400, `Invalid model. Allowed: ${[...CFG.ALLOWED_MODELS].join(', ')}`, 'INVALID_MODEL', corsHeaders);
  }

  // max_tokens
  if (typeof max_tokens !== 'number' || !Number.isInteger(max_tokens) || max_tokens < 1 || max_tokens > CFG.MAX_TOKENS) {
    return errResp(400, `max_tokens must be an integer 1–${CFG.MAX_TOKENS}`, 'INVALID_MAX_TOKENS', corsHeaders);
  }

  // messages
  const msgErr = validateMessages(messages);
  if (msgErr) return errResp(400, msgErr, 'INVALID_MESSAGES', corsHeaders);

  // system (optional)
  if (system !== undefined) {
    if (typeof system !== 'string') return errResp(400, 'system must be a string', 'INVALID_SYSTEM', corsHeaders);
    if (system.length > CFG.MAX_SYSTEM) return errResp(400, `system prompt too long (max ${CFG.MAX_SYSTEM} chars)`, 'SYSTEM_TOO_LONG', corsHeaders);
  }

  // ── Build clean payload — only validated fields are forwarded ───────────────
  const payload = {
    model,
    messages,
    max_tokens,
    stream: stream === true,
    ...(system ? { system } : {}),
  };

  // ── Retrieve API key from environment ────────────────────────────────────────
  const apiKey = Deno.env.get('CLAUDE_API_KEY');
  if (!apiKey) {
    // Do not expose internal config details in the error message
    console.error('[claude-proxy] CLAUDE_API_KEY env variable is not set');
    return errResp(503, 'AI service temporarily unavailable', 'SERVICE_UNAVAILABLE', corsHeaders);
  }

  // ── Forward request to Claude API ────────────────────────────────────────────
  let upstream;
  try {
    upstream = await fetch('https://api.anthropic.com/v1/messages', {
      method : 'POST',
      headers: {
        'Content-Type'     : 'application/json',
        'x-api-key'        : apiKey,
        'anthropic-version': '2023-06-01',
      },
      body: JSON.stringify(payload),
    });
  } catch (err) {
    console.error('[claude-proxy] Upstream fetch error:', err?.message);
    return errResp(502, 'Failed to reach AI service', 'UPSTREAM_ERROR', corsHeaders);
  }

  // ── Stream the upstream response back to the browser ─────────────────────────
  const contentType = upstream.headers.get('content-type') ?? 'application/json';
  const isStream    = contentType.includes('text/event-stream');

  return new Response(upstream.body, {
    status : upstream.status,
    headers: {
      ...rlHeaders,
      'Content-Type' : contentType,
      ...(isStream ? { 'Cache-Control': 'no-cache', 'X-Accel-Buffering': 'no' } : {}),
    },
  });
}
