/* Ambore — Supabase sync layer
 * Loads silently in the background alongside existing localStorage auth.
 * NEVER modifies localStorage behaviour — only syncs data to Supabase.
 */
(function () {
  'use strict';

  var SUPA_URL = 'https://mqonctgrvppdbjcuawue.supabase.co';
  var SUPA_KEY = 'eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6Im1xb25jdGdydnBwZGJqY3Vhd3VlIiwicm9sZSI6ImFub24iLCJpYXQiOjE3NzQwNTUwMzMsImV4cCI6MjA4OTYzMTAzM30.xc47ksXn5lLzF9w70U5BpCI86yzivsjbHUsJCk2ZseU';

  // ── Helpers ────────────────────────────────────────────────────────────────
  function headers() {
    return {
      'Content-Type': 'application/json',
      'apikey': SUPA_KEY,
      'Authorization': 'Bearer ' + SUPA_KEY,
      'Prefer': 'resolution=merge-duplicates'
    };
  }

  function upsert(table, data) {
    return fetch(SUPA_URL + '/rest/v1/' + table, {
      method: 'POST',
      headers: Object.assign({}, headers(), { 'Prefer': 'resolution=merge-duplicates' }),
      body: JSON.stringify(data)
    }).catch(function () {}); // silent fail — never break the page
  }

  function insert(table, data) {
    return fetch(SUPA_URL + '/rest/v1/' + table, {
      method: 'POST',
      headers: headers(),
      body: JSON.stringify(data)
    }).catch(function () {});
  }

  function getFrom(table, filter) {
    return fetch(SUPA_URL + '/rest/v1/' + table + '?' + filter, {
      headers: headers()
    }).then(function (r) { return r.json(); }).catch(function () { return []; });
  }

  // ── Read local session ─────────────────────────────────────────────────────
  function getLocalUser() {
    try {
      var u = JSON.parse(localStorage.getItem('ambore_user') || 'null');
      if (!u || !u.email) return null;
      if (u.expiresAt && Date.now() > u.expiresAt) return null;
      return u;
    } catch (e) { return null; }
  }

  function getLocalDB() {
    try { return JSON.parse(localStorage.getItem('ambore_db') || '{}'); }
    catch (e) { return {}; }
  }

  // ── Sync functions ─────────────────────────────────────────────────────────

  // Sync user profile
  function syncUser(u) {
    return upsert('users', { id: u.email, email: u.email, name: u.name || u.email, picture: u.picture || '' });
  }

  // Sync career scores
  function syncScores(userId) {
    try {
      var s = JSON.parse(localStorage.getItem('ambore_career_scores') || 'null');
      if (!s) return;
      upsert('career_scores', {
        user_id: userId,
        overall: s.overall || 0,
        resume_score: s.resumeScore || 0,
        ats_score: s.atsScore || 0,
        interview_score: s.interviewScore || 0,
        updated_at: new Date().toISOString()
      });
    } catch (e) {}
  }

  // Sync saved jobs from localStorage to Supabase
  function syncSavedJobs(userId) {
    try {
      var db = getLocalDB();
      var jobs = db.savedJobs || [];
      jobs.forEach(function (j) {
        if (!j || !j.id) return;
        upsert('saved_jobs', {
          user_id: userId,
          job_id: String(j.id),
          job_data: j,
          saved_at: j.savedAt || new Date().toISOString()
        });
      });
    } catch (e) {}
  }

  // Sync activity log
  function syncActivity(userId) {
    try {
      var db = getLocalDB();
      var acts = (db.activity || []).slice(0, 20); // last 20 only
      acts.forEach(function (a, i) {
        insert('activity', {
          user_id: userId,
          type: a.type || 'unknown',
          metadata: { label: a.label },
          created_at: a.createdAt || new Date().toISOString()
        });
      });
    } catch (e) {}
  }

  // ── Public API ─────────────────────────────────────────────────────────────
  window.AmborDB = {
    // Call after login/signup
    onLogin: function (user) {
      if (!user || !user.email) return;
      syncUser(user).then(function () {
        syncScores(user.email);
        syncSavedJobs(user.email);
        syncActivity(user.email);
      });
    },

    // Save a job application
    saveApplication: function (userId, job, status) {
      status = status || 'applied';
      return upsert('applications', {
        user_id: userId,
        job_id: String(job.id || job.url),
        job_data: job,
        status: status,
        applied_at: new Date().toISOString(),
        updated_at: new Date().toISOString()
      });
    },

    // Update application status
    updateApplicationStatus: function (userId, jobId, status) {
      return fetch(SUPA_URL + '/rest/v1/applications?user_id=eq.' + encodeURIComponent(userId) + '&job_id=eq.' + encodeURIComponent(jobId), {
        method: 'PATCH',
        headers: headers(),
        body: JSON.stringify({ status: status, updated_at: new Date().toISOString() })
      }).catch(function () {});
    },

    // Get all applications for a user
    getApplications: function (userId) {
      return getFrom('applications', 'user_id=eq.' + encodeURIComponent(userId) + '&order=applied_at.desc');
    },

    // Save a resume
    saveResume: function (userId, content, filename, atsScore) {
      return upsert('resumes', {
        user_id: userId,
        content: content,
        filename: filename || 'resume.txt',
        ats_score: atsScore || 0
      });
    },

    // Get saved jobs from DB (cross-device)
    getSavedJobs: function (userId) {
      return getFrom('saved_jobs', 'user_id=eq.' + encodeURIComponent(userId) + '&order=saved_at.desc');
    },

    // Log activity event
    logActivity: function (userId, type, metadata) {
      return insert('activity', {
        user_id: userId,
        type: type,
        metadata: metadata || {},
        created_at: new Date().toISOString()
      });
    }
  };

  // ── Auto-sync on page load if already logged in ────────────────────────────
  document.addEventListener('DOMContentLoaded', function () {
    var u = getLocalUser();
    if (u) {
      window.AmborDB.onLogin(u);
    }
  });

})();
