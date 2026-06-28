/**
 * Offerly API Client — full-stack DB layer
 * Wraps all Netlify Function calls with localStorage cache for instant UI.
 * Pattern: show cached data instantly → sync from DB in background → update cache.
 */
(function(global){
'use strict';

var BASE = '/.netlify/functions';

// ── Session ────────────────────────────────────────────────────────────────────
function getUser(){
  try{
    var u=JSON.parse(localStorage.getItem('ambore_user')||'null');
    if(!u||!u.id||(u.expiresAt&&Date.now()>u.expiresAt))return null;
    return u;
  }catch(e){return null;}
}

// ── Core fetch wrapper ─────────────────────────────────────────────────────────
async function apiFetch(path, opts){
  try{
    var res=await fetch(BASE+path, Object.assign({headers:{'Content-Type':'application/json'}}, opts));
    var data=await res.json();
    if(!res.ok) throw new Error(data.error||'Request failed');
    return data;
  }catch(e){
    console.warn('[AmborAPI]', path, e.message);
    throw e;
  }
}

// ── Cache helpers ──────────────────────────────────────────────────────────────
function cacheGet(key){ try{return JSON.parse(localStorage.getItem(key)||'null');}catch(e){return null;} }
function cacheSet(key,val){ try{localStorage.setItem(key,JSON.stringify(val));}catch(e){} }

// ── Auth ───────────────────────────────────────────────────────────────────────
async function register(name, email, password){
  return apiFetch('/auth-register',{method:'POST',body:JSON.stringify({name,email,password})});
}
async function login(email, password){
  return apiFetch('/auth-login',{method:'POST',body:JSON.stringify({email,password})});
}
async function googleAuth(email, name, picture){
  return apiFetch('/auth-google',{method:'POST',body:JSON.stringify({email,name,picture})});
}

// ── Dashboard ──────────────────────────────────────────────────────────────────
async function getDashboard(){
  var u=getUser(); if(!u) return null;
  var data=await apiFetch('/dashboard-data?userId='+encodeURIComponent(u.id));
  cacheSet('ambore_dashboard_'+u.id, {data, ts:Date.now()});
  return data;
}
function getDashboardCache(){
  var u=getUser(); if(!u) return null;
  var c=cacheGet('ambore_dashboard_'+u.id);
  if(c&&Date.now()-c.ts<300000) return c.data; // 5-min cache
  return null;
}

// ── Applications ───────────────────────────────────────────────────────────────
async function getApplications(){
  var u=getUser(); if(!u) return [];
  var data=await apiFetch('/applications-list?userId='+encodeURIComponent(u.id));
  cacheSet('ambore_apps_db_'+u.id, data.applications);
  return data.applications;
}
async function saveApplication(app){
  var u=getUser(); if(!u) throw new Error('Not logged in');
  return apiFetch('/applications-save',{method:'POST',body:JSON.stringify({userId:u.id,...app})});
}
async function deleteApplication(id){
  var u=getUser(); if(!u) throw new Error('Not logged in');
  return apiFetch('/applications-delete',{method:'POST',body:JSON.stringify({userId:u.id,id})});
}

// ── Resumes ────────────────────────────────────────────────────────────────────
async function saveResume(resume){
  var u=getUser(); if(!u) throw new Error('Not logged in');
  return apiFetch('/resumes-save',{method:'POST',body:JSON.stringify({userId:u.id,...resume})});
}
async function deleteResume(id){
  var u=getUser(); if(!u) throw new Error('Not logged in');
  return apiFetch('/resumes-delete',{method:'POST',body:JSON.stringify({userId:u.id,id})});
}

// ── Saved Jobs ─────────────────────────────────────────────────────────────────
async function getSavedJobs(){
  var u=getUser(); if(!u) return {jobs:[],jobIds:[]};
  var data=await apiFetch('/jobs-saved-list?userId='+encodeURIComponent(u.id));
  cacheSet('ambore_saved_ids_'+u.id, data.jobIds);
  return data;
}
async function toggleSaveJob(jobId, jobData, save){
  var u=getUser(); if(!u) throw new Error('Not logged in');
  return apiFetch('/jobs-save-toggle',{method:'POST',body:JSON.stringify({userId:u.id,jobId,jobData,action:save?'save':'unsave'})});
}
function getSavedJobIdsCache(){
  var u=getUser(); if(!u) return [];
  return cacheGet('ambore_saved_ids_'+u.id)||[];
}

// ── Career Score ───────────────────────────────────────────────────────────────
async function updateCareerScore(scores){
  var u=getUser(); if(!u) throw new Error('Not logged in');
  var data=await apiFetch('/career-score-update',{method:'POST',body:JSON.stringify({userId:u.id,...scores})});
  cacheSet('ambore_career_scores', {
    overall:data.careerScore.overall,
    resume:data.careerScore.resumeScore,
    ats:data.careerScore.atsScore,
    interview:data.careerScore.interviewScore,
    ts:Date.now()
  });
  return data;
}

// ── Activity Log ───────────────────────────────────────────────────────────────
async function logActivity(type, metadata){
  var u=getUser(); if(!u) return;
  try{
    await apiFetch('/activity-log',{method:'POST',body:JSON.stringify({userId:u.id,type,metadata})});
  }catch(e){/* non-critical, fail silently */}
}

// ── Export ─────────────────────────────────────────────────────────────────────
global.AmborAPI = {
  getUser,
  register, login, googleAuth,
  getDashboard, getDashboardCache,
  getApplications, saveApplication, deleteApplication,
  saveResume, deleteResume,
  getSavedJobs, toggleSaveJob, getSavedJobIdsCache,
  updateCareerScore,
  logActivity,
};

// ── Back button — inject on all inner pages ────────────────────────────────────
(function(){
  var path = window.location.pathname.replace(/\/+$/,'') || '/';
  if(path === '/' || path === '') return; // homepage — no back button needed

  document.addEventListener('DOMContentLoaded', function(){
    var sb = document.querySelector('.sb');
    if(!sb) return; // only on sidebar pages

    var style = document.createElement('style');
    style.textContent =
      '.sb-back{display:flex;align-items:center;justify-content:center;width:44px;height:36px;' +
      'margin:0 auto 8px;border-radius:8px;background:rgba(255,255,255,0.06);border:1px solid rgba(255,255,255,0.1);' +
      'color:rgba(255,255,255,0.55);cursor:pointer;text-decoration:none;transition:all .15s;flex-shrink:0}' +
      '.sb-back:hover{background:rgba(255,255,255,0.12);color:#fff;border-color:rgba(255,255,255,0.22);transform:translateX(-2px)}' +
      '.sb-back svg{flex-shrink:0}';
    document.head.appendChild(style);

    var btn = document.createElement('a');
    btn.className = 'sb-back';
    btn.title = 'Back';
    btn.setAttribute('aria-label', 'Go back');
    btn.innerHTML = '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><path d="M19 12H5"/><polyline points="12 19 5 12 12 5"/></svg>';
    btn.addEventListener('click', function(e){
      e.preventDefault();
      if(document.referrer && document.referrer.indexOf(window.location.hostname) !== -1 && window.history.length > 1){
        window.history.back();
      } else {
        window.location.href = '/';
      }
    });

    // Insert right before the logo
    var logo = sb.querySelector('.sb-logo');
    if(logo) sb.insertBefore(btn, logo);
    else sb.insertBefore(btn, sb.firstChild);
  });
})();

})(window);
