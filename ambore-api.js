/**
 * Ambore API Client — full-stack DB layer
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

})(window);
