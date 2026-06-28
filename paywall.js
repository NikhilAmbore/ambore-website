/**
 * AstraOffer Paywall — global upgrade intercept, loaded on every tool page.
 *
 * What this does:
 *  1. Monkey-patches window.fetch to detect 402 UPGRADE_REQUIRED from /api/claude
 *  2. Shows a beautiful upgrade modal automatically — no page-level changes needed
 *  3. Shows a floating plan-status pill (bottom-right) with live usage
 *  4. Exposes window.AstraOfferPaywall.show() for any page to trigger manually
 *
 * Loaded via protect.js so it runs on every authenticated tool page.
 */
(function (global) {
  'use strict';

  if (global.__amborePWReady) return;
  global.__amborePWReady = true;

  // ── Preserve original fetch before any patch ────────────────────────────
  var _fetch = global.fetch;

  // ── Styles ────────────────────────────────────────────────────────────────
  var CSS = [
    /* overlay */
    '#apw-overlay{display:none;position:fixed;inset:0;z-index:99999;',
    'background:rgba(10,15,30,.72);backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px);',
    'align-items:center;justify-content:center;padding:20px;font-family:Inter,-apple-system,sans-serif}',
    '#apw-overlay.apw-open{display:flex}',

    /* box */
    '#apw-box{background:#fff;border-radius:22px;max-width:420px;width:100%;overflow:hidden;',
    'box-shadow:0 40px 100px rgba(0,0,0,.28),0 4px 20px rgba(0,0,0,.12);',
    'animation:apwUp .28s cubic-bezier(.34,1.4,.64,1)}',
    '@keyframes apwUp{from{opacity:0;transform:translateY(18px) scale(.97)}to{opacity:1;transform:none}}',

    /* header */
    '.apw-head{background:linear-gradient(135deg,#1d4ed8,#2563eb,#3b82f6);',
    'padding:30px 28px 26px;text-align:center;position:relative}',
    '.apw-close{position:absolute;top:14px;right:14px;background:rgba(255,255,255,.18);',
    'border:none;color:#fff;width:30px;height:30px;border-radius:50%;cursor:pointer;',
    'font-size:1rem;line-height:30px;text-align:center;transition:background .15s}',
    '.apw-close:hover{background:rgba(255,255,255,.32)}',
    '.apw-emoji{font-size:2.4rem;display:block;margin-bottom:10px}',
    '.apw-head h2{font-size:1.18rem;font-weight:800;color:#fff;margin:0 0 7px;line-height:1.25}',
    '.apw-head p{font-size:.87rem;color:rgba(255,255,255,.78);margin:0;line-height:1.5}',
    '.apw-head p strong{color:#fff}',

    /* body */
    '.apw-body{padding:24px 28px 28px}',
    '.apw-feats{display:flex;flex-direction:column;gap:11px;margin-bottom:18px}',
    '.apw-feat{display:flex;align-items:flex-start;gap:10px}',
    '.apw-feat-ck{width:20px;height:20px;background:#eff6ff;border-radius:6px;',
    'display:flex;align-items:center;justify-content:center;flex-shrink:0;margin-top:1px}',
    '.apw-feat-ck svg{color:#2563eb}',
    '.apw-feat-txt{font-size:.87rem;color:#334155;line-height:1.45}',
    '.apw-feat-txt strong{color:#0f172a}',

    /* price row */
    '.apw-price-row{background:#f8fafc;border:1.5px solid #e2e8f0;border-radius:14px;',
    'padding:14px 18px;margin-bottom:18px;display:flex;align-items:center;justify-content:space-between}',
    '.apw-price-left{display:flex;align-items:flex-end;gap:4px;line-height:1}',
    '.apw-price-val{font-size:2rem;font-weight:900;color:#0f172a}',
    '.apw-price-mo{font-size:.85rem;color:#64748b;margin-bottom:3px}',
    '.apw-price-note{font-size:.74rem;color:#64748b;text-align:right;line-height:1.5}',

    /* buttons */
    '.apw-btn-up{width:100%;padding:13px;border-radius:11px;border:none;cursor:pointer;',
    'background:linear-gradient(135deg,#1d4ed8,#2563eb);color:#fff;',
    'font-size:.96rem;font-weight:700;font-family:inherit;margin-bottom:9px;',
    'box-shadow:0 4px 14px rgba(37,99,235,.35);transition:all .15s}',
    '.apw-btn-up:hover{opacity:.9;transform:translateY(-1px);box-shadow:0 6px 22px rgba(37,99,235,.45)}',
    '.apw-btn-up:disabled{opacity:.55;cursor:not-allowed;transform:none}',
    '.apw-btn-later{width:100%;padding:10px;border-radius:11px;border:1.5px solid #e2e8f0;',
    'background:#fff;color:#64748b;font-size:.87rem;font-weight:500;font-family:inherit;cursor:pointer;transition:all .15s}',
    '.apw-btn-later:hover{background:#f8fafc;color:#1e293b;border-color:#cbd5e1}',

    /* floating plan pill */
    '#apw-pill{position:fixed;bottom:22px;right:22px;z-index:9000;display:none;',
    'background:#fff;border:1.5px solid #e2e8f0;border-radius:22px;',
    'padding:8px 14px;align-items:center;gap:9px;',
    'box-shadow:0 4px 24px rgba(0,0,0,.1);cursor:pointer;text-decoration:none;',
    'font-family:Inter,-apple-system,sans-serif;font-size:.8rem;',
    'transition:box-shadow .15s,transform .12s}',
    '#apw-pill:hover{box-shadow:0 8px 32px rgba(0,0,0,.15);transform:translateY(-2px)}',
    '#apw-pill.apw-pill-on{display:flex}',
    '.apw-dot{width:8px;height:8px;border-radius:50%;flex-shrink:0}',
    '.apw-dot-free{background:#f59e0b}',
    '.apw-dot-prem{background:#22c55e}',
    '.apw-pill-name{font-weight:700;color:#1e293b}',
    '.apw-pill-sub{color:#64748b;font-size:.74rem}',
    '.apw-pill-tag{background:#2563eb;color:#fff;padding:2px 9px;border-radius:10px;',
    'font-size:.7rem;font-weight:700;margin-left:2px;white-space:nowrap}',

    /* ── Mobile responsive ── */
    '@media(max-width:480px){',
    '#apw-overlay{padding:12px;align-items:flex-end}',
    '#apw-box{border-radius:20px 20px 14px 14px;max-height:92dvh;overflow-y:auto}',
    '.apw-head{padding:22px 20px 18px}',
    '.apw-emoji{font-size:1.9rem;margin-bottom:7px}',
    '.apw-head h2{font-size:1.06rem}',
    '.apw-body{padding:18px 20px 22px}',
    '.apw-feats{gap:9px;margin-bottom:14px}',
    '.apw-feat-txt{font-size:.82rem}',
    '.apw-price-row{padding:11px 14px;margin-bottom:14px}',
    '.apw-price-val{font-size:1.7rem}',
    '.apw-btn-up{padding:14px;font-size:.92rem}',
    '.apw-btn-later{padding:11px;font-size:.83rem}',
    '}',
    /* pill — hide sub-text on very narrow screens */
    '@media(max-width:380px){',
    '#apw-pill{bottom:14px;right:14px;padding:7px 11px;gap:7px}',
    '.apw-pill-sub{display:none}',
    '}',
  ].join('');

  function injectStyles() {
    if (document.getElementById('apw-styles')) return;
    var s = document.createElement('style');
    s.id = 'apw-styles';
    s.textContent = CSS;
    (document.head || document.documentElement).appendChild(s);
  }

  // ── Modal HTML ──────────────────────────────────────────────────────────
  var MODAL_HTML = [
    '<div id="apw-overlay">',
    '<div id="apw-box">',
    '<div class="apw-head">',
    '<button class="apw-close" id="apw-close-btn" aria-label="Close">&times;</button>',
    '<span class="apw-emoji">&#9889;</span>',
    '<h2 id="apw-title">Premium required for AI tools</h2>',
    '<p id="apw-desc">Upgrade to <strong>Premium</strong> from $29/month &mdash; 1,000 AI requests every month.</p>',
    '</div>',
    '<div class="apw-body">',
    '<div class="apw-feats">',
    '<div class="apw-feat">',
    '<div class="apw-feat-ck"><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6L9 17l-5-5"/></svg></div>',
    '<div class="apw-feat-txt"><strong>1,000 AI requests / month</strong> — resume builder, cover letters, interview prep &amp; more</div>',
    '</div>',
    '<div class="apw-feat">',
    '<div class="apw-feat-ck"><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6L9 17l-5-5"/></svg></div>',
    '<div class="apw-feat-txt">Every AI tool unlocked — ATS scorer, cover letters, LinkedIn &amp; more</div>',
    '</div>',
    '<div class="apw-feat">',
    '<div class="apw-feat-ck"><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6L9 17l-5-5"/></svg></div>',
    '<div class="apw-feat-txt">Cancel anytime &mdash; <strong>no long-term commitment</strong></div>',
    '</div>',
    '</div>',
    '<div class="apw-price-row">',
    '<div class="apw-price-left">',
    '<span class="apw-price-val">$29</span>',
    '<span class="apw-price-mo">&nbsp;/ month</span>',
    '</div>',
    '<div class="apw-price-note">Save up to 28% with a longer plan &bull; <a href="/pricing" style="color:#2563eb">See all plans</a></div>',
    '</div>',
    '<button class="apw-btn-up" id="apw-upgrade-btn">Upgrade to Premium &rarr;</button>',
    '<button class="apw-btn-later" id="apw-later-btn">Maybe later</button>',
    '<p style="text-align:center;margin:10px 0 0;font-size:.75rem;color:#94a3b8">',
    'Already paid? <button id="apw-restore-btn" style="background:none;border:none;color:#2563eb;font-size:.75rem;cursor:pointer;text-decoration:underline;padding:0">Restore access</button>',
    '</p>',
    '</div>',
    '</div>',
    '</div>',
  ].join('');

  function injectModal() {
    if (document.getElementById('apw-overlay')) return;
    var d = document.createElement('div');
    d.innerHTML = MODAL_HTML;
    document.body.appendChild(d.firstChild);

    document.getElementById('apw-close-btn').addEventListener('click', hide);
    document.getElementById('apw-later-btn').addEventListener('click', hide);
    document.getElementById('apw-upgrade-btn').addEventListener('click', doCheckout);
    document.getElementById('apw-restore-btn').addEventListener('click', doRestore);
    document.getElementById('apw-overlay').addEventListener('click', function (e) {
      if (e.target === this) hide();
    });
  }

  // ── Plan pill ──────────────────────────────────────────────────────────
  function injectPill() {
    if (document.getElementById('apw-pill')) return;
    var a = document.createElement('a');
    a.id = 'apw-pill';
    a.href = '/pricing';
    a.setAttribute('aria-label', 'View your plan');
    document.body.appendChild(a);
  }

  function updatePill(status) {
    var pill = document.getElementById('apw-pill');
    if (!pill || !status) return;

    if (status.plan === 'premium') {
      var rem = status.monthlyRemaining != null ? status.monthlyRemaining : '—';
      pill.innerHTML =
        '<span class="apw-dot apw-dot-prem"></span>' +
        '<span class="apw-pill-name">Premium</span>' +
        '<span class="apw-pill-sub">' + rem + ' AI left this month</span>';
      pill.className = 'apw-pill-on';
    } else {
      pill.innerHTML =
        '<span class="apw-dot apw-dot-free"></span>' +
        '<span class="apw-pill-name">Free Plan</span>' +
        '<span class="apw-pill-sub">Upgrade to unlock AI tools</span>' +
        '<span class="apw-pill-tag">Upgrade $29/mo</span>';
      pill.className = 'apw-pill-on';
    }
  }

  // ── Show / hide ────────────────────────────────────────────────────────
  function show(reason) {
    _showForReason(reason || 'free_limit_reached');
  }

  function hide() {
    var o = document.getElementById('apw-overlay');
    if (o) o.classList.remove('apw-open');
  }

  function _showForReason(reason) {
    injectStyles();
    injectModal();
    var title = document.getElementById('apw-title');
    var desc  = document.getElementById('apw-desc');
    var btn   = document.getElementById('apw-upgrade-btn');

    if (reason === 'monthly_limit_reached') {
      if (title) title.textContent = 'Monthly AI limit reached';
      if (desc)  desc.innerHTML = 'You\'ve used all <strong>1,000 AI requests</strong> this month. Your limit resets on your next billing date.';
    } else {
      if (title) title.textContent = 'Premium required for AI tools';
      if (desc)  desc.innerHTML = 'AI features require a <strong>Premium</strong> subscription &mdash; from $29/month for 1,000 AI requests.';
    }
    if (btn) { btn.disabled = false; btn.textContent = 'Upgrade to Premium →'; }

    var o = document.getElementById('apw-overlay');
    if (o) o.classList.add('apw-open');
  }

  // ── Checkout ──────────────────────────────────────────────────────────
  async function doCheckout() {
    var btn = document.getElementById('apw-upgrade-btn');
    if (btn) { btn.disabled = true; btn.textContent = 'Redirecting to payment…'; }

    try {
      var user = null;
      try { user = JSON.parse(localStorage.getItem('ambore_user') || 'null'); } catch (e) {}

      if (!user || !user.id) {
        window.location.href = '/?auth=login&redirect=/pricing&msg=Log+in+to+upgrade+to+Premium';
        return;
      }

      var res = await _fetch('/.netlify/functions/create-checkout', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ userId: user.id, plan: 'monthly' }),
      });

      if (res.status === 409) {
        hide();
        if (btn) { btn.disabled = false; btn.textContent = 'Upgrade to Premium →'; }
        alert('You already have an active Premium subscription!');
        return;
      }

      var data;
      try { data = await res.json(); } catch (jsonErr) {
        throw new Error('Unexpected server response (status ' + res.status + '). Please try again.');
      }

      if (!res.ok) throw new Error(data.error || 'Failed to start checkout');
      if (data.url) { window.location.href = data.url; return; }
      throw new Error('No checkout URL returned');

    } catch (e) {
      if (btn) { btn.disabled = false; btn.textContent = 'Upgrade to Premium →'; }
      alert('Payment error: ' + e.message + '\n\nVisit astraoffer.org/pricing to upgrade.');
    }
  }

  // ── Restore access (for users who already paid) ───────────────────────
  async function doRestore() {
    var btn = document.getElementById('apw-restore-btn');
    if (btn) { btn.disabled = true; btn.textContent = 'Checking…'; }

    try {
      var user = null;
      try { user = JSON.parse(localStorage.getItem('ambore_user') || 'null'); } catch (e) {}
      if (!user || !user.id) {
        window.location.href = '/?auth=login&redirect=' + encodeURIComponent(window.location.pathname);
        return;
      }

      var res = await _fetch('/.netlify/functions/verify-payment', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ userId: user.id }),
      });
      var data = await res.json();

      if (data.plan === 'premium') {
        hide();
        // Reload the page so the user can proceed without the paywall
        window.location.reload();
      } else {
        if (btn) { btn.disabled = false; btn.textContent = 'Restore access'; }
        alert('No active Premium subscription found for ' + (user.email || 'your account') + '.\n\nIf you just paid, please wait 1–2 minutes and try again, or contact support at amborenikhil46@gmail.com.');
      }
    } catch (e) {
      if (btn) { btn.disabled = false; btn.textContent = 'Restore access'; }
      alert('Could not verify subscription: ' + e.message);
    }
  }

  // ── Load subscription status ──────────────────────────────────────────
  function loadPlanStatus() {
    try {
      var user = JSON.parse(localStorage.getItem('ambore_user') || 'null');
      if (!user || !user.id) return;

      _fetch('/.netlify/functions/subscription-status?userId=' + encodeURIComponent(user.id))
        .then(function (r) { return r.json(); })
        .then(function (s) {
          global.__amborePlan = s;
          updatePill(s);
        })
        .catch(function () {});
    } catch (e) {}
  }

  // ── Fetch interceptor ─────────────────────────────────────────────────
  // 1. Auto-injects X-User-ID on every /api/claude call so the edge function
  //    can identify the user for subscription enforcement.
  // 2. Catches 402 UPGRADE_REQUIRED and shows the paywall modal.
  global.fetch = function () {
    var args = Array.prototype.slice.call(arguments);
    var url  = typeof args[0] === 'string' ? args[0]
             : (args[0] && args[0].url ? args[0].url : '');

    if (url.indexOf('/api/claude') !== -1) {
      // Prefer AstraOfferSecurity, fall back to localStorage directly so mobile
      // browsers that haven't fully loaded AstraOfferSecurity still get the header.
      var uid = '';
      try {
        uid = (global.AstraOfferSecurity && global.AstraOfferSecurity.getUserId())
              ? global.AstraOfferSecurity.getUserId()
              : '';
      } catch (e) {}
      if (!uid) {
        try {
          var _u = JSON.parse(localStorage.getItem('ambore_user') || 'null');
          uid = (_u && _u.id) ? String(_u.id) : '';
        } catch (e) {}
      }
      var opts = args[1] ? Object.assign({}, args[1]) : {};
      var hdrs = new Headers(opts.headers || {});
      if (!hdrs.has('X-User-ID')) hdrs.set('X-User-ID', uid || 'anonymous');
      opts.headers = hdrs;
      args[1] = opts;
    }

    return _fetch.apply(global, args).then(function (res) {
      if (res.status === 402 && url.indexOf('/api/claude') !== -1) {
        // Show modal and swallow the response so the page's own error handler
        // never fires (no "API error 402" message shown).
        // Pages can register window.__onApiPaywall(reason) to handle 402 themselves
        // (e.g. resume page shows a preview lock). If it returns true, skip the modal.
        res.clone().json().then(function (data) {
          var reason = (data && data.reason) ? data.reason : 'free_limit_reached';
          var resolvedReason = (data && data.code === 'UPGRADE_REQUIRED') ? reason : 'free_limit_reached';
          var handled = typeof global.__onApiPaywall === 'function' && global.__onApiPaywall(resolvedReason, data);
          if (!handled) _showForReason(resolvedReason);
        }).catch(function () {
          var handled = typeof global.__onApiPaywall === 'function' && global.__onApiPaywall('free_limit_reached', null);
          if (!handled) _showForReason('free_limit_reached');
        });
        return new Promise(function () {}); // never resolves — page error handler skipped
      }
      return res;
    });
  };

  // ── Public API ────────────────────────────────────────────────────────
  global.AstraOfferPaywall = { show: show, hide: hide, _checkout: doCheckout };

  // ── Boot on DOM ready ─────────────────────────────────────────────────
  function boot() {
    injectStyles();
    injectModal();
    injectPill();
    loadPlanStatus();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }

}(window));
