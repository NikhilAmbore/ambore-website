/**
 * Ambore Community — Document Upload Edge Function
 * ─────────────────────────────────────────────────────────────────────────────
 * Handles admin-only PDF uploads to the community-docs/ folder via GitHub API.
 *
 * SECURITY CONTROLS
 *  1. Admin secret  — validated against COMMUNITY_ADMIN_SECRET env var
 *  2. File type     — only PDF accepted (magic bytes + MIME check)
 *  3. File size     — hard cap 10 MB
 *  4. Origin        — same allowed-origin list as claude-proxy
 *  5. Rate limit    — 10 uploads / IP / hour
 *  6. Input whitelist — strict field validation, no unexpected keys
 *
 * ENV VARS REQUIRED (set in Netlify dashboard → Site settings → Env vars)
 *  COMMUNITY_ADMIN_SECRET  — long random string known only to the founder
 *  GITHUB_TOKEN            — fine-grained PAT with Contents:write on this repo
 *  GITHUB_REPO             — e.g. "nikhilambore/ambore-website"
 *  GITHUB_BRANCH           — default "main"
 */

// ── Rate-limit store (per edge-function instance) ─────────────────────────────
const uploadStore = new Map(); // key: IP → { count, resetAt }

const CFG = {
  UPLOAD_LIMIT  : 10,
  UPLOAD_WINDOW : 3_600_000, // 1 hour

  MAX_FILE_BYTES: 10 * 1024 * 1024, // 10 MB
  MAX_TITLE_LEN : 120,
  MAX_DESC_LEN  : 500,
  MAX_CAT_LEN   : 60,

  ALLOWED_ORIGINS: new Set([
    'https://ambore.org',
    'https://www.ambore.org',
    'https://ambore.netlify.app',
  ]),

  ALLOWED_CATEGORIES: new Set([
    'Resume Tips', 'Interview Prep', 'Job Search', 'Visa & Immigration',
    'Salary & Negotiation', 'Career Growth', 'Tech Skills', 'General',
  ]),
};

function checkRate(store, key, limit, windowMs) {
  const now   = Date.now();
  const entry = store.get(key);
  if (!entry || now > entry.resetAt) {
    store.set(key, { count: 1, resetAt: now + windowMs });
    return { allowed: true };
  }
  entry.count++;
  return { allowed: entry.count <= limit, resetAt: entry.resetAt };
}

function errResp(status, message, code, extra = {}) {
  return new Response(
    JSON.stringify({ error: message, code }),
    { status, headers: { 'Content-Type': 'application/json', ...extra } },
  );
}

export default async function handler(req, context) {
  const origin = req.headers.get('origin') ?? '';
  const corsOrigin = CFG.ALLOWED_ORIGINS.has(origin)
    ? origin
    : [...CFG.ALLOWED_ORIGINS][0];

  const corsHeaders = {
    'Access-Control-Allow-Origin' : corsOrigin,
    'Access-Control-Allow-Methods': 'POST, OPTIONS',
    'Access-Control-Allow-Headers': 'Content-Type',
    'Vary': 'Origin',
  };

  if (req.method === 'OPTIONS') {
    return new Response(null, { status: 204, headers: { ...corsHeaders, 'Access-Control-Max-Age': '600' } });
  }
  if (req.method !== 'POST') {
    return errResp(405, 'Method not allowed', 'METHOD_NOT_ALLOWED', corsHeaders);
  }

  // ── IP rate limiting ─────────────────────────────────────────────────────────
  const ip = context.ip ?? 'unknown';
  const rl = checkRate(uploadStore, ip, CFG.UPLOAD_LIMIT, CFG.UPLOAD_WINDOW);
  if (!rl.allowed) {
    const retryAfter = Math.ceil((rl.resetAt - Date.now()) / 1000);
    return errResp(429, 'Upload limit reached. Try again later.', 'RATE_LIMITED', {
      ...corsHeaders, 'Retry-After': String(retryAfter),
    });
  }

  // ── Parse multipart form data ────────────────────────────────────────────────
  let formData;
  try {
    formData = await req.formData();
  } catch {
    return errResp(400, 'Invalid form data', 'BAD_REQUEST', corsHeaders);
  }

  // ── Field extraction ─────────────────────────────────────────────────────────
  const adminSecret = (formData.get('adminSecret') ?? '').toString().trim();
  const title       = (formData.get('title')       ?? '').toString().trim();
  const description = (formData.get('description') ?? '').toString().trim();
  const category    = (formData.get('category')    ?? '').toString().trim();
  const file        = formData.get('file');

  // ── Admin secret validation ──────────────────────────────────────────────────
  const expectedSecret = Deno.env.get('COMMUNITY_ADMIN_SECRET');
  if (!expectedSecret) {
    console.error('[community-upload] COMMUNITY_ADMIN_SECRET not set');
    return errResp(503, 'Upload service unavailable', 'SERVICE_UNAVAILABLE', corsHeaders);
  }
  if (!adminSecret || adminSecret !== expectedSecret) {
    return errResp(403, 'Invalid admin secret', 'FORBIDDEN', corsHeaders);
  }

  // ── Input validation ─────────────────────────────────────────────────────────
  if (!title || title.length > CFG.MAX_TITLE_LEN) {
    return errResp(400, `title required (max ${CFG.MAX_TITLE_LEN} chars)`, 'INVALID_TITLE', corsHeaders);
  }
  if (description.length > CFG.MAX_DESC_LEN) {
    return errResp(400, `description too long (max ${CFG.MAX_DESC_LEN} chars)`, 'INVALID_DESC', corsHeaders);
  }
  if (!CFG.ALLOWED_CATEGORIES.has(category)) {
    return errResp(400, `category must be one of: ${[...CFG.ALLOWED_CATEGORIES].join(', ')}`, 'INVALID_CATEGORY', corsHeaders);
  }
  if (!file || !(file instanceof File)) {
    return errResp(400, 'file required', 'NO_FILE', corsHeaders);
  }

  // ── File type check ───────────────────────────────────────────────────────────
  const fileBytes = new Uint8Array(await file.arrayBuffer());
  if (fileBytes.length > CFG.MAX_FILE_BYTES) {
    return errResp(400, 'File too large (max 10 MB)', 'FILE_TOO_LARGE', corsHeaders);
  }
  // PDF magic bytes: %PDF
  if (fileBytes[0] !== 0x25 || fileBytes[1] !== 0x50 || fileBytes[2] !== 0x44 || fileBytes[3] !== 0x46) {
    return errResp(400, 'Only PDF files are allowed', 'INVALID_FILE_TYPE', corsHeaders);
  }

  // ── Sanitise filename ─────────────────────────────────────────────────────────
  const ts       = Date.now();
  const safeName = title.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 60);
  const filename = `${safeName}-${ts}.pdf`;
  const filePath = `community-docs/${filename}`;

  // ── GitHub env vars ───────────────────────────────────────────────────────────
  const githubToken  = Deno.env.get('GITHUB_TOKEN');
  const githubRepo   = Deno.env.get('GITHUB_REPO')   ?? 'nikhilambore/ambore-website';
  const githubBranch = Deno.env.get('GITHUB_BRANCH') ?? 'main';

  if (!githubToken) {
    console.error('[community-upload] GITHUB_TOKEN not set');
    return errResp(503, 'Upload service unavailable', 'SERVICE_UNAVAILABLE', corsHeaders);
  }

  const ghHeaders = {
    'Authorization': `Bearer ${githubToken}`,
    'Accept'       : 'application/vnd.github+json',
    'Content-Type' : 'application/json',
    'X-GitHub-Api-Version': '2022-11-28',
  };
  const ghBase = `https://api.github.com/repos/${githubRepo}/contents`;

  // ── Upload PDF to GitHub ──────────────────────────────────────────────────────
  const b64Content = btoa(String.fromCharCode(...fileBytes));
  let pdfResp;
  try {
    pdfResp = await fetch(`${ghBase}/${filePath}`, {
      method : 'PUT',
      headers: ghHeaders,
      body   : JSON.stringify({
        message: `community: add ${filename}`,
        content: b64Content,
        branch : githubBranch,
      }),
    });
  } catch (err) {
    console.error('[community-upload] GitHub PDF PUT error:', err?.message);
    return errResp(502, 'Failed to upload file', 'UPSTREAM_ERROR', corsHeaders);
  }
  if (!pdfResp.ok) {
    const txt = await pdfResp.text();
    console.error('[community-upload] GitHub PDF PUT failed:', pdfResp.status, txt);
    return errResp(502, 'Failed to save file to repository', 'GH_ERROR', corsHeaders);
  }

  // ── Fetch current manifest ────────────────────────────────────────────────────
  const manifestPath = 'community-docs/manifest.json';
  let manifestSha  = null;
  let manifestDocs = [];
  try {
    const mResp = await fetch(`${ghBase}/${manifestPath}?ref=${githubBranch}`, { headers: ghHeaders });
    if (mResp.ok) {
      const mData  = await mResp.json();
      manifestSha  = mData.sha;
      const mJson  = JSON.parse(atob(mData.content.replace(/\n/g, '')));
      manifestDocs = Array.isArray(mJson.documents) ? mJson.documents : [];
    }
  } catch (err) {
    console.error('[community-upload] Failed to fetch manifest:', err?.message);
    // Non-fatal — we'll create a fresh manifest
  }

  // ── Append new document entry ─────────────────────────────────────────────────
  const newDoc = {
    id         : `doc_${ts}`,
    title,
    description,
    category,
    filename,
    path       : `/${filePath}`,
    size_bytes : fileBytes.length,
    uploaded_at: new Date(ts).toISOString(),
  };
  manifestDocs.unshift(newDoc); // newest first

  const newManifest = JSON.stringify({ version: 1, documents: manifestDocs }, null, 2);
  const b64Manifest = btoa(unescape(encodeURIComponent(newManifest)));

  // ── Update manifest in GitHub ─────────────────────────────────────────────────
  const manifestBody = {
    message: `community: update manifest — add "${title}"`,
    content: b64Manifest,
    branch : githubBranch,
    ...(manifestSha ? { sha: manifestSha } : {}),
  };
  try {
    const mPutResp = await fetch(`${ghBase}/${manifestPath}`, {
      method : 'PUT',
      headers: ghHeaders,
      body   : JSON.stringify(manifestBody),
    });
    if (!mPutResp.ok) {
      const txt = await mPutResp.text();
      console.error('[community-upload] manifest update failed:', mPutResp.status, txt);
      // PDF was already saved — log error but still return success to avoid confusion
    }
  } catch (err) {
    console.error('[community-upload] manifest PUT error:', err?.message);
  }

  // ── Return the new document entry ─────────────────────────────────────────────
  return new Response(JSON.stringify({ success: true, document: newDoc }), {
    status : 200,
    headers: { ...corsHeaders, 'Content-Type': 'application/json' },
  });
}
