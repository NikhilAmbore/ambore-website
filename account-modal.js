/**
 * account-modal.js — shared across all tool pages
 * Injects: My Account button in sidebar, 3-tab modal (Account / Base Resume / Pipeline), onboarding checklist
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
  function fmtDate(iso) {
    if (!iso) return '—';
    var d = new Date(iso);
    return d.toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
  }

  /* ═══════════════════════════════════════════════════════════════
     CSS
  ═══════════════════════════════════════════════════════════════ */
  var style = document.createElement('style');
  style.textContent = [
    /* overlay */
    '.acct-modal-overlay{display:none;position:fixed;inset:0;z-index:10000;background:rgba(13,27,75,0.55);backdrop-filter:blur(4px);align-items:center;justify-content:center;padding:16px}',
    '.acct-modal-overlay.open{display:flex}',
    '.acct-modal{background:#fff;border-radius:20px;width:100%;max-width:460px;max-height:90vh;overflow:hidden;box-shadow:0 24px 64px rgba(0,0,0,0.18);font-family:inherit;display:flex;flex-direction:column}',
    /* header */
    '.acct-header{background:linear-gradient(135deg,#2563EB,#1D4ED8);padding:22px 24px 0;position:relative;flex-shrink:0}',
    '.acct-close{position:absolute;top:12px;right:12px;width:28px;height:28px;border-radius:50%;background:rgba(255,255,255,0.18);border:none;color:#fff;font-size:1rem;cursor:pointer;display:flex;align-items:center;justify-content:center;line-height:1;font-family:inherit}',
    '.acct-user-row{display:flex;align-items:center;gap:14px;margin-bottom:14px}',
    '.acct-avatar{width:44px;height:44px;border-radius:50%;background:rgba(255,255,255,0.2);border:2px solid rgba(255,255,255,0.35);display:flex;align-items:center;justify-content:center;font-size:1.1rem;font-weight:900;color:#fff;flex-shrink:0}',
    '.acct-name{font-size:0.95rem;font-weight:800;color:#fff;margin-bottom:2px}',
    '.acct-email{font-size:0.72rem;color:rgba(255,255,255,0.7)}',
    '.acct-plan-badge{display:inline-flex;align-items:center;gap:5px;margin-top:4px;padding:2px 9px;border-radius:20px;font-size:0.65rem;font-weight:700;text-transform:uppercase;letter-spacing:0.06em}',
    '.acct-plan-badge.free{background:rgba(255,255,255,0.15);color:#fff}',
    '.acct-plan-badge.premium{background:rgba(251,191,36,0.25);color:#fbbf24;border:1px solid rgba(251,191,36,0.4)}',
    /* tabs */
    '.acct-tabs{display:flex;border-bottom:none;margin-top:0}',
    '.acct-tab{flex:1;padding:10px 6px 8px;text-align:center;font-size:0.72rem;font-weight:700;color:rgba(255,255,255,0.5);cursor:pointer;border-bottom:2px solid transparent;transition:all 0.2s;letter-spacing:0.02em;text-transform:uppercase}',
    '.acct-tab.active{color:#fff;border-bottom-color:#fff}',
    /* panels */
    '.acct-panels{overflow-y:auto;flex:1}',
    '.acct-panel{display:none}',
    '.acct-panel.active{display:block}',
    /* account panel */
    '.acct-body{padding:18px 22px}',
    '.acct-row{display:flex;align-items:center;justify-content:space-between;padding:10px 0;border-bottom:1px solid #F1F5F9}',
    '.acct-row:last-child{border-bottom:none}',
    '.acct-row-label{font-size:0.78rem;color:#64748B;font-weight:500}',
    '.acct-row-val{font-size:0.82rem;color:#1e293b;font-weight:700}',
    '.acct-footer{padding:14px 22px;background:#F8FAFC;border-top:1px solid #E2E8F0;display:flex;gap:10px;flex-shrink:0}',
    '.acct-btn{flex:1;padding:9px;border-radius:9px;font-size:0.82rem;font-weight:700;cursor:pointer;border:none;font-family:inherit;transition:opacity 0.2s}',
    '.acct-btn-upgrade{background:linear-gradient(135deg,#2563EB,#1D4ED8);color:#fff}',
    '.acct-btn-upgrade:hover{opacity:0.88}',
    '.acct-btn-logout{background:rgba(239,68,68,0.08);color:#ef4444;border:1px solid rgba(239,68,68,0.2)}',
    '.acct-btn-logout:hover{background:rgba(239,68,68,0.15)}',
    /* base resume panel */
    '.br-body{padding:18px 22px}',
    '.br-label{font-size:0.7rem;font-weight:700;text-transform:uppercase;letter-spacing:0.07em;color:#64748B;margin-bottom:8px}',
    '.br-hint{font-size:0.72rem;color:#94A3B8;margin-bottom:12px;line-height:1.5}',
    '.br-textarea{width:100%;height:180px;padding:10px 13px;background:#F8FAFC;border:1px solid #E2E8F0;border-radius:10px;font-size:0.8rem;color:#1e293b;resize:none;font-family:inherit;outline:none;line-height:1.5}',
    '.br-textarea:focus{border-color:#2563EB}',
    '.br-actions{display:flex;align-items:center;gap:10px;margin-top:12px}',
    '.br-save-btn{padding:8px 18px;background:linear-gradient(135deg,#2563EB,#1D4ED8);border:none;border-radius:8px;color:#fff;font-size:0.82rem;font-weight:700;cursor:pointer;font-family:inherit}',
    '.br-clear-btn{padding:8px 14px;background:none;border:1px solid #E2E8F0;border-radius:8px;color:#94A3B8;font-size:0.78rem;font-weight:600;cursor:pointer;font-family:inherit}',
    '.br-clear-btn:hover{border-color:#94A3B8;color:#475569}',
    '.br-status{font-size:0.72rem;color:#22c55e;margin-left:auto;display:none}',
    /* pipeline panel */
    '.pl-body{padding:14px 16px}',
    '.pl-empty{text-align:center;padding:32px 16px;color:#94A3B8;font-size:0.82rem}',
    '.pl-remind-banner{background:rgba(239,68,68,0.06);border:1px solid rgba(239,68,68,0.2);border-radius:10px;padding:10px 14px;margin-bottom:12px;font-size:0.75rem;color:#dc2626;font-weight:600;display:flex;align-items:center;gap:6px}',
    '.pl-card{background:#F8FAFC;border:1px solid #E2E8F0;border-radius:11px;padding:11px 13px;margin-bottom:8px}',
    '.pl-card.overdue{border-color:rgba(239,68,68,0.25);background:rgba(239,68,68,0.03)}',
    '.pl-card-top{display:flex;align-items:flex-start;gap:8px;margin-bottom:8px}',
    '.pl-title{font-size:0.82rem;font-weight:700;color:#1e293b;line-height:1.3;flex:1}',
    '.pl-company{font-size:0.7rem;color:#64748B;margin-top:1px}',
    '.pl-status-btn{padding:3px 9px;border-radius:20px;font-size:0.65rem;font-weight:700;cursor:pointer;border:none;font-family:inherit;white-space:nowrap;flex-shrink:0}',
    '.pl-st-tracking{background:rgba(99,102,241,0.1);color:#6366f1}',
    '.pl-st-applied{background:rgba(37,99,235,0.1);color:#2563EB}',
    '.pl-st-phone{background:rgba(251,191,36,0.15);color:#d97706}',
    '.pl-st-interview{background:rgba(168,85,247,0.12);color:#9333ea}',
    '.pl-st-offer{background:rgba(34,197,94,0.12);color:#16a34a}',
    '.pl-st-rejected{background:rgba(239,68,68,0.1);color:#dc2626}',
    '.pl-card-foot{display:flex;align-items:center;gap:8px}',
    '.pl-date-input{flex:1;padding:4px 8px;border:1px solid #E2E8F0;border-radius:6px;font-size:0.7rem;color:#64748B;background:#fff;font-family:inherit}',
    '.pl-date-label{font-size:0.68rem;color:#94A3B8;white-space:nowrap}',
    '.pl-del{padding:4px 8px;border:1px solid #E2E8F0;border-radius:6px;font-size:0.65rem;color:#94A3B8;cursor:pointer;background:none;font-family:inherit}',
    '.pl-del:hover{color:#ef4444;border-color:rgba(239,68,68,0.3)}',
    /* sidebar account button */
    '.sb-acct-btn{display:flex;flex-direction:column;align-items:center;justify-content:center;width:60px;min-height:56px;border-radius:12px;color:rgba(255,255,255,0.55);text-decoration:none;font-size:0.58rem;font-weight:600;gap:4px;cursor:pointer;background:none;border:none;transition:background 0.15s,color 0.15s;padding:6px 4px;font-family:inherit;text-align:center;line-height:1.2}',
    '.sb-acct-btn:hover{background:rgba(255,255,255,0.08);color:rgba(255,255,255,0.9)}',
    '.sb-acct-avatar{width:26px;height:26px;border-radius:50%;background:rgba(99,102,241,0.35);border:1.5px solid rgba(129,140,248,0.5);display:flex;align-items:center;justify-content:center;font-size:0.72rem;font-weight:900;color:#a5b4fc;position:relative}',
    '.sb-remind-dot{position:absolute;top:-2px;right:-2px;width:8px;height:8px;border-radius:50%;background:#ef4444;border:1.5px solid #0d1b4b}',
  ].join('');
  document.head.appendChild(style);

  /* ═══════════════════════════════════════════════════════════════
     PIPELINE HELPERS
  ═══════════════════════════════════════════════════════════════ */
  var STATUSES = ['tracking','applied','phone_screen','interview','offer','rejected'];
  var STATUS_LABELS = {tracking:'Tracking',applied:'Applied',phone_screen:'Phone Screen',interview:'Interview',offer:'Offer 🎉',rejected:'Rejected'};
  var STATUS_CSS = {tracking:'pl-st-tracking',applied:'pl-st-applied',phone_screen:'pl-st-phone',interview:'pl-st-interview',offer:'pl-st-offer',rejected:'pl-st-rejected'};

  function getApps() {
    try { return JSON.parse(localStorage.getItem('ambore_applications') || '[]'); } catch(e) { return []; }
  }
  function saveApps(apps) {
    try { localStorage.setItem('ambore_applications', JSON.stringify(apps)); } catch(e) {}
  }
  function getFollowups() {
    try { return JSON.parse(localStorage.getItem('ao_followup_dates') || '{}'); } catch(e) { return {}; }
  }
  function saveFollowups(fu) {
    try { localStorage.setItem('ao_followup_dates', JSON.stringify(fu)); } catch(e) {}
  }
  function overdueCount() {
    var fu = getFollowups(); var today = new Date().toISOString().slice(0,10); var n = 0;
    Object.values(fu).forEach(function(d){ if (d && d <= today) n++; });
    return n;
  }

  /* ═══════════════════════════════════════════════════════════════
     MODAL
  ═══════════════════════════════════════════════════════════════ */
  var overlay = el('div', {'class':'acct-modal-overlay','id':'acct-modal-overlay'});
  var modal   = el('div', {'class':'acct-modal'});
  overlay.appendChild(modal);

  overlay.addEventListener('click', function(e){ if(e.target===overlay) closeModal(); });
  document.addEventListener('keydown', function(e){ if(e.key==='Escape') closeModal(); });

  function closeModal() { overlay.classList.remove('open'); }
  window.__closeAccountModal = closeModal;

  var _activeTab = 'account';
  function switchTab(tab) {
    _activeTab = tab;
    modal.querySelectorAll('.acct-tab').forEach(function(t){ t.classList.toggle('active', t.dataset.tab===tab); });
    modal.querySelectorAll('.acct-panel').forEach(function(p){ p.classList.toggle('active', p.dataset.panel===tab); });
  }

  function buildModal() {
    var user = getUser();
    var name = (user && user.name) ? user.name : ((user && user.email) ? user.email.split('@')[0] : 'User');
    var email = (user && user.email) ? user.email : '—';
    var isPremium = user && (user.plan === 'premium' || user.isPremium);
    var initial = name.charAt(0).toUpperCase();
    var joined = (user && user.createdAt) ? new Date(user.createdAt).toLocaleDateString('en-US',{month:'short',year:'numeric'}) : '—';
    var baseResume = localStorage.getItem('ao_base_resume') || '';
    var apps = getApps();
    var fu = getFollowups();
    var today = new Date().toISOString().slice(0,10);
    var overdue = overdueCount();
    var logoutFn = (typeof logout !== 'undefined') ? 'logout()' : 'localStorage.removeItem(\'ambore_user\');window.location.href=\'/\'';

    modal.innerHTML = [
      /* header */
      '<div class="acct-header">',
        '<button class="acct-close" onclick="window.__closeAccountModal()">&times;</button>',
        '<div class="acct-user-row">',
          '<div class="acct-avatar">'+initial+'</div>',
          '<div><div class="acct-name">'+name+'</div>',
          '<div class="acct-email">'+email+'</div>',
          '<span class="acct-plan-badge '+(isPremium?'premium':'free')+'">'+(isPremium?'⭐ Premium':'✦ Free Plan')+'</span></div>',
        '</div>',
        '<div class="acct-tabs">',
          '<div class="acct-tab'+(  _activeTab==='account' ?' active':'')+'" data-tab="account"  onclick="window.__acctTab(\'account\')">Account</div>',
          '<div class="acct-tab'+(_activeTab==='resume'?' active':'')+'" data-tab="resume"   onclick="window.__acctTab(\'resume\')">Base Resume</div>',
          '<div class="acct-tab'+(_activeTab==='pipeline'?' active':'')+'" data-tab="pipeline" onclick="window.__acctTab(\'pipeline\')">'+(overdue?'Pipeline &#128308;':'Pipeline')+'</div>',
        '</div>',
      '</div>',

      /* panels */
      '<div class="acct-panels">',

        /* Account panel */
        '<div class="acct-panel'+(_activeTab==='account'?' active':'')+'" data-panel="account">',
          '<div class="acct-body">',
            '<div class="acct-row"><span class="acct-row-label">Plan</span><span class="acct-row-val">'+(isPremium?'Premium — $29/mo':'Free')+'</span></div>',
            '<div class="acct-row"><span class="acct-row-label">AI Requests</span><span class="acct-row-val">'+(isPremium?'1,000/mo':'Limited')+'</span></div>',
            '<div class="acct-row"><span class="acct-row-label">Member Since</span><span class="acct-row-val">'+joined+'</span></div>',
            '<div class="acct-row"><span class="acct-row-label">Applications Tracked</span><span class="acct-row-val">'+apps.length+'</span></div>',
          '</div>',
          '<div class="acct-footer">',
            isPremium ? '' : '<button class="acct-btn acct-btn-upgrade" onclick="window.location.href=\'/pricing\'">Upgrade to Premium</button>',
            '<button class="acct-btn acct-btn-logout" onclick="'+logoutFn+'">Log Out</button>',
          '</div>',
        '</div>',

        /* Base Resume panel */
        '<div class="acct-panel'+(_activeTab==='resume'?' active':'')+'" data-panel="resume">',
          '<div class="br-body">',
            '<div class="br-label">Your Master Resume</div>',
            '<div class="br-hint">Paste your resume once. It auto-fills the Resume, ATS Score, and Cover Letter tools so you never paste it again.</div>',
            '<textarea class="br-textarea" id="acct-br-textarea" placeholder="Paste your full resume here...">'+baseResume.replace(/</g,'&lt;')+'</textarea>',
            '<div class="br-actions">',
              '<button class="br-save-btn" onclick="window.__saveBaseResume()">Save Resume</button>',
              '<button class="br-clear-btn" onclick="window.__clearBaseResume()">Clear</button>',
              '<span class="br-status" id="br-status">Saved!</span>',
            '</div>',
          '</div>',
        '</div>',

        /* Pipeline panel */
        '<div class="acct-panel'+(_activeTab==='pipeline'?' active':'')+'" data-panel="pipeline">',
          '<div class="pl-body" id="pl-body">',
            buildPipelineHTML(apps, fu, today, overdue),
          '</div>',
        '</div>',

      '</div>',
    ].join('');
  }

  function buildPipelineHTML(apps, fu, today, overdue) {
    if (!apps.length) {
      return '<div class="pl-empty">No applications yet.<br>Save jobs from the Jobs page to track them here.</div>';
    }
    var rows = [];
    if (overdue) {
      rows.push('<div class="pl-remind-banner">⏰ '+overdue+' follow-up'+(overdue>1?'s':'')+' due — check below</div>');
    }
    var sorted = apps.slice().sort(function(a,b){ return new Date(b.updated_at||b.applied_at) - new Date(a.updated_at||a.applied_at); });
    sorted.forEach(function(app) {
      var jid = app.job_id;
      var jd = app.job_data || {};
      var status = app.status || 'tracking';
      var followUpDate = fu[jid] || '';
      var isOverdue = followUpDate && followUpDate <= today;
      rows.push(
        '<div class="pl-card'+(isOverdue?' overdue':'')+'" id="pl-card-'+jid+'">',
          '<div class="pl-card-top">',
            '<div style="flex:1">',
              '<div class="pl-title">'+(jd.title||'Job').replace(/</g,'&lt;')+'</div>',
              '<div class="pl-company">'+(jd.company||'').replace(/</g,'&lt;')+(jd.location?' · '+jd.location:'')+'</div>',
            '</div>',
            '<button class="pl-status-btn '+STATUS_CSS[status]+'" onclick="window.__cycleStatus(\''+jid+'\')">'+STATUS_LABELS[status]+'</button>',
          '</div>',
          '<div class="pl-card-foot">',
            '<span class="pl-date-label">Follow-up:</span>',
            '<input type="date" class="pl-date-input" value="'+followUpDate+'" onchange="window.__setFollowup(\''+jid+'\',this.value)" title="Set follow-up reminder"/>',
            jd.url ? '<a href="'+jd.url+'" target="_blank" rel="noopener" style="font-size:0.7rem;color:#2563EB;text-decoration:none;white-space:nowrap">View →</a>' : '',
            '<button class="pl-del" onclick="window.__deleteApp(\''+jid+'\')">✕</button>',
          '</div>',
        '</div>'
      );
    });
    return rows.join('');
  }

  /* pipeline actions */
  window.__cycleStatus = function(jid) {
    var apps = getApps();
    var idx = apps.findIndex(function(a){ return a.job_id === jid; });
    if (idx < 0) return;
    var cur = apps[idx].status || 'tracking';
    var next = STATUSES[(STATUSES.indexOf(cur) + 1) % STATUSES.length];
    apps[idx].status = next;
    apps[idx].updated_at = new Date().toISOString();
    saveApps(apps);
    var btn = document.querySelector('#pl-card-'+jid+' .pl-status-btn');
    if (btn) { btn.textContent = STATUS_LABELS[next]; btn.className = 'pl-status-btn '+STATUS_CSS[next]; }
  };
  window.__setFollowup = function(jid, date) {
    var fu = getFollowups();
    if (date) fu[jid] = date; else delete fu[jid];
    saveFollowups(fu);
    var card = document.getElementById('pl-card-'+jid);
    if (card) {
      var today = new Date().toISOString().slice(0,10);
      card.classList.toggle('overdue', !!(date && date <= today));
    }
    updateRemindDot();
  };
  window.__deleteApp = function(jid) {
    if (!confirm('Remove this application from tracking?')) return;
    var apps = getApps().filter(function(a){ return a.job_id !== jid; });
    saveApps(apps);
    var fu = getFollowups(); delete fu[jid]; saveFollowups(fu);
    var card = document.getElementById('pl-card-'+jid);
    if (card) card.remove();
    updateRemindDot();
  };
  window.__acctTab = function(tab) { switchTab(tab); };

  /* base resume actions */
  window.__saveBaseResume = function() {
    var ta = document.getElementById('acct-br-textarea');
    if (!ta) return;
    localStorage.setItem('ao_base_resume', ta.value.trim());
    var st = document.getElementById('br-status');
    if (st) { st.style.display='inline'; clearTimeout(st._t); st._t=setTimeout(function(){ st.style.display='none'; }, 1800); }
  };
  window.__clearBaseResume = function() {
    var ta = document.getElementById('acct-br-textarea');
    if (ta) ta.value = '';
    localStorage.removeItem('ao_base_resume');
  };

  function openModal(tab) {
    buildModal();
    overlay.classList.add('open');
    if (tab) switchTab(tab);
  }
  window.__openAccountModal = openModal;

  function updateRemindDot() {
    var dot = document.querySelector('.sb-remind-dot');
    var n = overdueCount();
    if (dot) dot.style.display = n ? '' : 'none';
  }

  /* ═══════════════════════════════════════════════════════════════
     SIDEBAR BUTTON
  ═══════════════════════════════════════════════════════════════ */
  function injectSidebarBtn() {
    document.body.appendChild(overlay);
    var sbFoot = document.querySelector('.sb-foot');
    if (!sbFoot) return;
    var user = getUser();
    var name = (user && user.name) ? user.name : ((user && user.email) ? user.email.split('@')[0] : 'Me');
    var initial = name.charAt(0).toUpperCase();
    var n = overdueCount();

    var btn = el('button', {'class':'sb-acct-btn','title':'My Account','onclick':'window.__openAccountModal&&window.__openAccountModal()'});
    btn.innerHTML = '<div class="sb-acct-avatar">'+initial+'<span class="sb-remind-dot" style="display:'+(n?'':'none')+'"></span></div><span>Account</span>';
    sbFoot.insertBefore(btn, sbFoot.firstChild);
  }

  /* ═══════════════════════════════════════════════════════════════
     AUTO-FILL BASE RESUME on tool pages
  ═══════════════════════════════════════════════════════════════ */
  function autoFillBaseResume() {
    var base = localStorage.getItem('ao_base_resume');
    if (!base) return;
    // Try after a short delay so page init (showApp/init) can run first
    setTimeout(function() {
      var ta = document.getElementById('resume-text');
      if (ta && !ta.value.trim()) {
        ta.value = base;
        // Trigger the right tab switch per page
        if (typeof setResumeMode === 'function') setResumeMode('paste');
        else if (typeof switchTab === 'function') switchTab('paste');
      }
    }, 200);
  }

  /* ═══════════════════════════════════════════════════════════════
     2. ONBOARDING CHECKLIST
  ═══════════════════════════════════════════════════════════════ */
  function injectOnboarding() {
    if (localStorage.getItem('ao_onboarding_dismissed')) return;
    var user = getUser();
    if (!user) return;

    var steps = [
      { key:'ao_did_resume',  label:'Generate your first resume',  href:'/resume' },
      { key:'ao_did_ats',     label:'Check your ATS match score',   href:'/ats-score' },
      { key:'ao_did_cover',   label:'Create a cover letter',        href:'/cover-letter' },
    ];

    var allDone = steps.every(function(s){ return !!localStorage.getItem(s.key); });
    if (allDone) { localStorage.setItem('ao_onboarding_dismissed','1'); return; }

    var obStyle = document.createElement('style');
    obStyle.textContent = [
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
    document.head.appendChild(obStyle);

    var completed = steps.filter(function(s){ return !!localStorage.getItem(s.key); }).length;
    var stepsHtml = steps.map(function(s){
      var done = !!localStorage.getItem(s.key);
      return '<a href="'+s.href+'" class="ob-step'+(done?' done':'')+'"><div class="ob-check">'+(done?'✓':'')+'</div><div class="ob-step-label">'+s.label+'</div></a>';
    }).join('');

    var panel = el('div', {'class':'ob-panel','id':'ob-panel'});
    panel.innerHTML = [
      '<div class="ob-head"><div><div class="ob-title">🚀 Getting Started</div><div class="ob-sub">'+completed+' of '+steps.length+' complete</div></div>',
      '<button class="ob-close" onclick="document.getElementById(\'ob-panel\').remove();localStorage.setItem(\'ao_onboarding_dismissed\',\'1\')">&times;</button></div>',
      '<div class="ob-steps">'+stepsHtml+'</div>',
      '<div class="ob-footer">Click any step to get started</div>',
    ].join('');

    function show() { document.body.appendChild(panel); }
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', show);
    else show();
  }

  /* ── run ── */
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function() {
      injectSidebarBtn();
      injectOnboarding();
      autoFillBaseResume();
    });
  } else {
    injectSidebarBtn();
    injectOnboarding();
    autoFillBaseResume();
  }

})();
