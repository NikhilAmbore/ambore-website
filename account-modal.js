/**
 * account-modal.js — shared across all tool pages
 * Injects: My Account button in sidebar, account modal, onboarding checklist
 */
(function () {
  'use strict';

  /* ── helpers ── */
  function getUser() {
    try { return JSON.parse(localStorage.getItem('ambore_user') || 'null'); } catch(e) { return null; }
  }
  function el(tag, attrs, html) {
    var d = document.createElement(tag);
    Object.keys(attrs || {}).forEach(function(k){ d.setAttribute(k, attrs[k]); });
    if (html !== undefined) d.innerHTML = html;
    return d;
  }

  /* ═══════════════════════════════════════════════════════════════
     1. MY ACCOUNT MODAL
  ═══════════════════════════════════════════════════════════════ */
  function injectAccountModal() {
    var style = document.createElement('style');
    style.textContent = [
      '.acct-modal-overlay{display:none;position:fixed;inset:0;z-index:10000;background:rgba(13,27,75,0.55);backdrop-filter:blur(4px);align-items:center;justify-content:center}',
      '.acct-modal-overlay.open{display:flex}',
      '.acct-modal{background:#fff;border-radius:20px;width:100%;max-width:400px;overflow:hidden;box-shadow:0 24px 64px rgba(0,0,0,0.18);font-family:inherit}',
      '.acct-header{background:linear-gradient(135deg,#2563EB,#1D4ED8);padding:28px 28px 22px;position:relative}',
      '.acct-close{position:absolute;top:14px;right:14px;width:30px;height:30px;border-radius:50%;background:rgba(255,255,255,0.18);border:none;color:#fff;font-size:1.1rem;cursor:pointer;display:flex;align-items:center;justify-content:center;line-height:1}',
      '.acct-avatar{width:52px;height:52px;border-radius:50%;background:rgba(255,255,255,0.2);border:2px solid rgba(255,255,255,0.35);display:flex;align-items:center;justify-content:center;font-size:1.3rem;font-weight:900;color:#fff;margin-bottom:12px}',
      '.acct-name{font-size:1.05rem;font-weight:800;color:#fff;margin-bottom:2px}',
      '.acct-email{font-size:0.78rem;color:rgba(255,255,255,0.7)}',
      '.acct-plan-badge{display:inline-flex;align-items:center;gap:5px;margin-top:10px;padding:3px 10px;border-radius:20px;font-size:0.7rem;font-weight:700;text-transform:uppercase;letter-spacing:0.06em}',
      '.acct-plan-badge.free{background:rgba(255,255,255,0.15);color:#fff}',
      '.acct-plan-badge.premium{background:rgba(251,191,36,0.25);color:#fbbf24;border:1px solid rgba(251,191,36,0.4)}',
      '.acct-body{padding:20px 24px}',
      '.acct-row{display:flex;align-items:center;justify-content:space-between;padding:12px 0;border-bottom:1px solid #F1F5F9}',
      '.acct-row:last-child{border-bottom:none}',
      '.acct-row-label{font-size:0.8rem;color:#64748B;font-weight:500}',
      '.acct-row-val{font-size:0.85rem;color:#1e293b;font-weight:700}',
      '.acct-footer{padding:16px 24px;background:#F8FAFC;border-top:1px solid #E2E8F0;display:flex;gap:10px}',
      '.acct-btn{flex:1;padding:10px;border-radius:10px;font-size:0.85rem;font-weight:700;cursor:pointer;border:none;font-family:inherit;transition:opacity 0.2s}',
      '.acct-btn-upgrade{background:linear-gradient(135deg,#2563EB,#1D4ED8);color:#fff}',
      '.acct-btn-upgrade:hover{opacity:0.88}',
      '.acct-btn-logout{background:rgba(239,68,68,0.08);color:#ef4444;border:1px solid rgba(239,68,68,0.2)}',
      '.acct-btn-logout:hover{background:rgba(239,68,68,0.15)}',
      /* sb account button */
      '.sb-acct-btn{display:flex;flex-direction:column;align-items:center;justify-content:center;width:60px;min-height:56px;border-radius:12px;color:rgba(255,255,255,0.55);text-decoration:none;font-size:0.58rem;font-weight:600;gap:4px;cursor:pointer;background:none;border:none;transition:background 0.15s,color 0.15s;padding:6px 4px;font-family:inherit;text-align:center;line-height:1.2}',
      '.sb-acct-btn:hover{background:rgba(255,255,255,0.08);color:rgba(255,255,255,0.9)}',
      '.sb-acct-avatar{width:26px;height:26px;border-radius:50%;background:rgba(99,102,241,0.35);border:1.5px solid rgba(129,140,248,0.5);display:flex;align-items:center;justify-content:center;font-size:0.72rem;font-weight:900;color:#a5b4fc}',
    ].join('');
    document.head.appendChild(style);

    /* modal HTML */
    var overlay = el('div', {'class':'acct-modal-overlay', 'id':'acct-modal-overlay'});
    var modal = el('div', {'class':'acct-modal'});
    overlay.appendChild(modal);
    document.body.appendChild(overlay);

    overlay.addEventListener('click', function(e){ if(e.target===overlay) closeModal(); });

    function openModal() {
      var user = getUser();
      var name = (user && user.name) ? user.name : ((user && user.email) ? user.email.split('@')[0] : 'User');
      var email = (user && user.email) ? user.email : '—';
      var isPremium = user && (user.plan === 'premium' || user.isPremium);
      var initial = name.charAt(0).toUpperCase();
      var joined = (user && user.createdAt) ? new Date(user.createdAt).toLocaleDateString('en-US',{month:'short',year:'numeric'}) : '—';

      modal.innerHTML = [
        '<div class="acct-header">',
          '<button class="acct-close" onclick="document.getElementById(\'acct-modal-overlay\').classList.remove(\'open\')">&times;</button>',
          '<div class="acct-avatar">'+initial+'</div>',
          '<div class="acct-name">'+name+'</div>',
          '<div class="acct-email">'+email+'</div>',
          '<span class="acct-plan-badge '+(isPremium?'premium':'free')+'">',
            isPremium ? '⭐ Premium' : '✦ Free Plan',
          '</span>',
        '</div>',
        '<div class="acct-body">',
          '<div class="acct-row"><span class="acct-row-label">Plan</span><span class="acct-row-val">'+(isPremium?'Premium — $29/mo':'Free')+'</span></div>',
          '<div class="acct-row"><span class="acct-row-label">AI Requests</span><span class="acct-row-val">'+(isPremium?'1,000/mo':'Limited')+'</span></div>',
          '<div class="acct-row"><span class="acct-row-label">Member Since</span><span class="acct-row-val">'+joined+'</span></div>',
          '<div class="acct-row"><span class="acct-row-label">Email</span><span class="acct-row-val" style="font-size:0.78rem;color:#64748B">'+email+'</span></div>',
        '</div>',
        '<div class="acct-footer">',
          isPremium ? '' : '<button class="acct-btn acct-btn-upgrade" onclick="window.location.href=\'/pricing\'">Upgrade to Premium</button>',
          '<button class="acct-btn acct-btn-logout" onclick="'+(typeof logout!=='undefined'?'logout()':'localStorage.removeItem(\'ambore_user\');window.location.href=\'/\'')+'">Log Out</button>',
        '</div>',
      ].join('');
      overlay.classList.add('open');
    }
    function closeModal() { overlay.classList.remove('open'); }
    window.__openAccountModal = openModal;

    /* inject account button into sidebar footer (above logout) */
    function injectSidebarBtn() {
      var sbFoot = document.querySelector('.sb-foot');
      if (!sbFoot) return;
      var user = getUser();
      var name = (user && user.name) ? user.name : ((user && user.email) ? user.email.split('@')[0] : 'Me');
      var initial = name.charAt(0).toUpperCase();

      var btn = el('button', {'class':'sb-acct-btn', 'title':'My Account', 'onclick':'window.__openAccountModal&&window.__openAccountModal()'});
      btn.innerHTML = '<div class="sb-acct-avatar">'+initial+'</div><span>Account</span>';
      sbFoot.insertBefore(btn, sbFoot.firstChild);
    }
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', injectSidebarBtn);
    } else {
      injectSidebarBtn();
    }
  }

  /* ═══════════════════════════════════════════════════════════════
     2. ONBOARDING CHECKLIST (shows once, floats bottom-right)
  ═══════════════════════════════════════════════════════════════ */
  function injectOnboarding() {
    if (localStorage.getItem('ao_onboarding_dismissed')) return;
    var user = getUser();
    if (!user) return;

    var steps = [
      { key:'ao_did_resume',   label:'Generate your first resume',       href:'/resume' },
      { key:'ao_did_ats',      label:'Check your ATS match score',        href:'/ats-score' },
      { key:'ao_did_cover',    label:'Create a cover letter',             href:'/cover-letter' },
    ];

    var allDone = steps.every(function(s){ return !!localStorage.getItem(s.key); });
    if (allDone) { localStorage.setItem('ao_onboarding_dismissed','1'); return; }

    var style = document.createElement('style');
    style.textContent = [
      '.ob-panel{position:fixed;bottom:24px;right:24px;width:270px;background:#fff;border:1px solid #E2E8F0;border-radius:16px;box-shadow:0 8px 32px rgba(0,0,0,0.12);z-index:9000;overflow:hidden;animation:ob-slide-in 0.4s ease}',
      '@keyframes ob-slide-in{from{opacity:0;transform:translateY(16px)}to{opacity:1;transform:translateY(0)}}',
      '.ob-head{background:linear-gradient(135deg,#2563EB,#1D4ED8);padding:14px 16px;display:flex;align-items:center;justify-content:space-between}',
      '.ob-title{font-size:0.82rem;font-weight:800;color:#fff}',
      '.ob-sub{font-size:0.68rem;color:rgba(255,255,255,0.7);margin-top:2px}',
      '.ob-close{background:rgba(255,255,255,0.18);border:none;color:#fff;width:22px;height:22px;border-radius:50%;cursor:pointer;font-size:0.85rem;display:flex;align-items:center;justify-content:center;flex-shrink:0;font-family:inherit}',
      '.ob-steps{padding:12px 14px;display:flex;flex-direction:column;gap:8px}',
      '.ob-step{display:flex;align-items:center;gap:10px;padding:8px 10px;border-radius:10px;text-decoration:none;transition:background 0.15s}',
      '.ob-step:hover{background:#F8FAFC}',
      '.ob-step.done{opacity:0.45;pointer-events:none}',
      '.ob-check{width:20px;height:20px;border-radius:50%;border:2px solid #E2E8F0;flex-shrink:0;display:flex;align-items:center;justify-content:center;font-size:0.65rem}',
      '.ob-step.done .ob-check{background:#22c55e;border-color:#22c55e;color:#fff}',
      '.ob-step:not(.done) .ob-check{background:#fff}',
      '.ob-step-label{font-size:0.78rem;font-weight:600;color:#1e293b;line-height:1.3}',
      '.ob-step.done .ob-step-label{text-decoration:line-through;color:#94A3B8}',
      '.ob-footer{padding:10px 14px;border-top:1px solid #F1F5F9;font-size:0.68rem;color:#94A3B8;text-align:center}',
    ].join('');
    document.head.appendChild(style);

    var completed = steps.filter(function(s){ return !!localStorage.getItem(s.key); }).length;

    var stepsHtml = steps.map(function(s){
      var done = !!localStorage.getItem(s.key);
      return '<a href="'+s.href+'" class="ob-step'+(done?' done':'')+'">'
        +'<div class="ob-check">'+(done?'✓':'')+'</div>'
        +'<div class="ob-step-label">'+s.label+'</div>'
        +'</a>';
    }).join('');

    var panel = el('div', {'class':'ob-panel', 'id':'ob-panel'});
    panel.innerHTML = [
      '<div class="ob-head">',
        '<div><div class="ob-title">🚀 Getting Started</div><div class="ob-sub">'+completed+' of '+steps.length+' complete</div></div>',
        '<button class="ob-close" onclick="document.getElementById(\'ob-panel\').remove();localStorage.setItem(\'ao_onboarding_dismissed\',\'1\')">&times;</button>',
      '</div>',
      '<div class="ob-steps">'+stepsHtml+'</div>',
      '<div class="ob-footer">Click any step to get started</div>',
    ].join('');

    function show() { document.body.appendChild(panel); }
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', show);
    } else {
      show();
    }
  }

  /* ── run ── */
  injectAccountModal();
  injectOnboarding();

})();
