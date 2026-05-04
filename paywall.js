/**
 * Ambore Paywall — global upgrade intercept, loaded on every tool page.
 *
 * What this does:
 *  1. Monkey-patches window.fetch to detect 402 UPGRADE_REQUIRED from /api/claude
 *  2. Shows a beautiful upgrade modal automatically — no page-level changes needed
 *  3. Shows a floating plan-status pill (bottom-right) with live usage
 *  4. Exposes window.AmborePaywall.show() for any page to trigger manually
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
    '<h2 id="apw-title">You\'ve used your free AI request</h2>',
    '<p id="apw-desc">Upgrade to <strong>Premium</strong> — 100 AI requests every month.</p>',
    '</div>',
    '<div class="apw-body">',
    '<div class="apw-feats">',
    '<div class="apw-feat">',
    '<div class="apw-feat-ck"><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6L9 17l-5-5"/></svg></div>',
    '<div class="apw-feat-txt"><strong>100 AI requests / month</strong> — resume builder, cover letters, interview prep &amp; more</div>',
    '</div>',
    '<div class="apw-feat">',
    '<div class="apw-feat-ck"><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6L9 17l-5-5"/></svg></div>',
    '<div class="apw-feat-txt">Every AI tool unlocked — ATS scorer, interview AI, coding, LinkedIn, portfolio &amp; more</div>',
    '</div>',
    '<div class="apw-feat">',
    '<div class="apw-feat-ck"><svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" stroke-linejoin="round"><path d="M20 6L9 17l-5-5"/></svg></div>',
    '<div class="apw-feat-txt">Cancel anytime &mdash; <strong>no long-term commitment</strong></div>',
    '</div>',
    '</div>',
    '<div class="apw-price-row">',
    '<div class="apw-price-left">',
    '<span class="apw-price-val">$9</span>',
    '<span class="apw-price-mo">&nbsp;/ month</span>',
    '</div>',
    '<div class="apw-price-note">Billed monthly via<br/>Dodo Payments &bull; Cancel anytime</div>',
    '</div>',
    '<button class="apw-btn-up" id="apw-upgrade-btn">Upgrade to Premium &rarr;</button>',
    '<button class="apw-btn-later" id="apw-later-btn">Maybe later</button>',
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
      var freeRem = status.freeRemaining != null ? status.freeRemaining : 0;
      pill.innerHTML =
        '<span class="apw-dot apw-dot-free"></span>' +
        '<span class="apw-pill-name">Free Plan</span>' +
        '<span class="apw-pill-sub">' + freeRem + ' free AI use left</span>' +
        '<span class="apw-pill-tag">Upgrade $9/mo</span>';
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
      if (desc)  desc.innerHTML = 'You\'ve used all <strong>100 AI requests</strong> this month. Upgrade renews on your billing date.';
    } else {
      if (title) title.textContent = 'You\'ve used your free AI request';
      if (desc)  desc.innerHTML = 'Upgrade to <strong>Premium</strong> for $9/month &mdash; 100 AI requests every month.';
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
        body: JSON.stringify({ userId: user.id }),
      });

      var data = await res.json();

      if (res.status === 409) {
        hide();
        if (btn) { btn.disabled = false; btn.textContent = 'Upgrade to Premium →'; }
        alert('You already have an active Premium subscription!');
        return;
      }

      if (!res.ok) throw new Error(data.error || 'Failed to start checkout');
      if (data.url) { window.location.href = data.url; return; }
      throw new Error('No checkout URL returned');

    } catch (e) {
      if (btn) { btn.disabled = false; btn.textContent = 'Upgrade to Premium →'; }
      alert('Payment error: ' + e.message + '\n\nVisit ambore.org/pricing to upgrade.');
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
      var uid = global.AmboreSecurity ? global.AmboreSecurity.getUserId() : '';
      if (uid) {
        var opts = args[1] ? Object.assign({}, args[1]) : {};
        var hdrs = new Headers(opts.headers || {});
        if (!hdrs.has('X-User-ID')) hdrs.set('X-User-ID', uid);
        opts.headers = hdrs;
        args[1] = opts;
      }
    }

    return _fetch.apply(global, args).then(function (res) {
      if (res.status === 402 && url.indexOf('/api/claude') !== -1) {
        res.clone().json().then(function (data) {
          var reason = (data && data.reason) ? data.reason : 'free_limit_reached';
          if (data && data.code === 'UPGRADE_REQUIRED') {
            setTimeout(function () { _showForReason(reason); }, 80);
          }
        }).catch(function () {
          setTimeout(function () { _showForReason('free_limit_reached'); }, 80);
        });
      }
      return res;
    });
  };

  // ── Public API ────────────────────────────────────────────────────────
  global.AmborePaywall = { show: show, hide: hide, _checkout: doCheckout };

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
