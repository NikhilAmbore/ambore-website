/* © 2025 Ambore.org — All rights reserved. Unauthorized copying is prohibited. */
(function(){
  'use strict';

  /* ── 1. Disable right-click context menu ── */
  document.addEventListener('contextmenu', function(e){
    e.preventDefault();
    return false;
  }, true);

  /* ── 2. Block keyboard shortcuts ── */
  document.addEventListener('keydown', function(e){
    var ctrl = e.ctrlKey || e.metaKey; // Ctrl on Windows/Linux, Cmd on Mac

    // F12 — Open DevTools
    if (e.key === 'F12') { e.preventDefault(); return false; }

    if (ctrl) {
      // Ctrl+Shift+I / J / C — DevTools panels
      if (e.shiftKey && /^[ijcIJC]$/.test(e.key)) { e.preventDefault(); return false; }
      // Ctrl+U — View Source
      if (/^[uU]$/.test(e.key)) { e.preventDefault(); return false; }
      // Ctrl+S — Save Page As
      if (/^[sS]$/.test(e.key)) { e.preventDefault(); return false; }
      // Ctrl+P — Print (reveals source layout)
      if (/^[pP]$/.test(e.key)) { e.preventDefault(); return false; }
    }
  }, true);

  /* ── 3. Block drag-to-copy on images and links ── */
  document.addEventListener('dragstart', function(e){
    if (e.target && (e.target.tagName === 'IMG' || e.target.tagName === 'A')) {
      e.preventDefault();
    }
  });

  /* ── 4. Disable text selection (allow inputs, textareas, contenteditable) ── */
  var style = document.createElement('style');
  style.textContent =
    'body *:not(input):not(textarea):not([contenteditable="true"]){' +
    '-webkit-user-select:none!important;-moz-user-select:none!important;' +
    '-ms-user-select:none!important;user-select:none!important}';
  document.head.appendChild(style);

  /* ── 5. Console warning ── */
  setTimeout(function(){
    try {
      console.clear();
      console.log(
        '%c⛔  STOP!',
        'color:#ef4444;font-size:44px;font-weight:900;font-family:monospace'
      );
      console.log(
        '%c This site is protected by copyright.\n © ' +
        new Date().getFullYear() +
        ' Ambore.org — All rights reserved.\n Unauthorized copying or reproduction is strictly prohibited.',
        'color:#e2e8f0;font-size:13px;background:#0d1117;padding:12px 16px;' +
        'border-radius:6px;border-left:3px solid #ef4444;font-family:monospace;line-height:1.7'
      );
    } catch(err) {}
  }, 600);

})();

/**
 * AmboreSecurity — client-side security utilities
 * ─────────────────────────────────────────────────────────────────────────────
 * Used by every tool page that calls the /api/claude proxy.
 *
 * 1. Rate limiting   — prevents abusive bursts from a single browser session
 *                      (server-side IP rate limiting in the edge function is
 *                       the primary control; this is a defence-in-depth layer)
 * 2. Input sanitization — strips null bytes, enforces length limits, trims
 * 3. getUserId       — returns a stable user identifier for the X-User-ID
 *                       header sent to the edge function's per-user rate limiter
 *
 * OWASP A01 (Broken Access Control) — getUserId validates session expiry
 * OWASP A03 (Injection)             — sanitizeInput strips dangerous chars
 */
window.AmboreSecurity = (function () {
  'use strict';

  // ── Client-side rate-limit config ──────────────────────────────────────────
  // Generous limits so legitimate use is never blocked client-side;
  // the edge function applies the true hard limits.
  var CLIENT_LIMITS = {
    ai: { max: 40, windowMs: 3600000 },  // 40 AI calls per browser session / hour
  };

  /**
   * Check and increment a client-side token bucket stored in localStorage.
   * Returns { allowed: bool, remaining: int, retryAt: timestamp|null }
   */
  function checkRateLimit(feature) {
    var cfg  = CLIENT_LIMITS[feature] || { max: 30, windowMs: 3600000 };
    var key  = '_rl_' + feature;
    var now  = Date.now();
    var raw  = null;
    try { raw = JSON.parse(localStorage.getItem(key) || 'null'); } catch (e) {}

    if (!raw || now > raw.resetAt) {
      var next = { count: 1, resetAt: now + cfg.windowMs };
      try { localStorage.setItem(key, JSON.stringify(next)); } catch (e) {}
      return { allowed: true, remaining: cfg.max - 1, retryAt: null };
    }

    raw.count++;
    try { localStorage.setItem(key, JSON.stringify(raw)); } catch (e) {}

    if (raw.count > cfg.max) {
      return { allowed: false, remaining: 0, retryAt: raw.resetAt };
    }
    return { allowed: true, remaining: cfg.max - raw.count, retryAt: null };
  }

  /**
   * Sanitize a string input before it is sent to the AI proxy.
   *  - Removes null bytes (can confuse parsers / cause injection)
   *  - Removes non-printable control characters (keeps \n and \t)
   *  - Trims leading/trailing whitespace
   *  - Hard-truncates to maxLen characters
   */
  function sanitizeInput(str, maxLen) {
    if (typeof str !== 'string') return '';
    maxLen = (typeof maxLen === 'number' && maxLen > 0) ? maxLen : 32000;
    return str
      .replace(/\0/g, '')                               // null bytes
      .replace(/[\x01-\x08\x0B\x0C\x0E-\x1F\x7F]/g, '') // control chars (keep \n \t)
      .trim()
      .slice(0, maxLen);
  }

  /**
   * Return the authenticated user's id (string) or empty string.
   * Validates that the session has not expired — returns '' if expired.
   */
  function getUserId() {
    try {
      var u = JSON.parse(localStorage.getItem('ambore_user') || 'null');
      if (!u || !u.id) return '';
      if (u.expiresAt && Date.now() > u.expiresAt) return '';
      return String(u.id).slice(0, 64);
    } catch (e) {
      return '';
    }
  }

  /**
   * Build the standard fetch headers for an /api/claude proxy request.
   * Includes the X-User-ID header for server-side per-user rate limiting.
   */
  function proxyHeaders() {
    var h   = { 'Content-Type': 'application/json' };
    var uid = getUserId();
    if (uid) h['X-User-ID'] = uid;
    return h;
  }

  return {
    checkRateLimit : checkRateLimit,
    sanitizeInput  : sanitizeInput,
    getUserId      : getUserId,
    proxyHeaders   : proxyHeaders,
  };
}());

// Auto-load paywall on every page that includes protect.js
(function(){
  if (window.__amborePWLoaded) return;
  window.__amborePWLoaded = true;
  var s = document.createElement('script');
  s.src = '/paywall.js';
  (document.head || document.documentElement).appendChild(s);
}());
