'use client';

// ─── Mirrors the exact auth system from the existing Ambore HTML site ────────
// Storage keys: ambore_db (users + session), ambore_user (flat session for tools)
// Password hashing: SHA-256 with "ambore2025:" prefix — same as the old site

export const GOOGLE_CLIENT_ID =
  '288905989713-qa7ha78cpf9jt5ch5u361uu7ck495n2e.apps.googleusercontent.com';

export interface AmborUser {
  email: string;
  name: string;
  picture?: string;
}

export interface AmborSession {
  user: AmborUser;
  expires: number; // ms timestamp
}

export interface AmborDB {
  users?: Record<string, { name: string; hash: string; created: number }>;
  session?: AmborSession;
}

export interface AmborUserFlat {
  id: string;
  email: string;
  name: string;
  picture: string;
  expiresAt: number;
}

// ── Raw DB helpers ─────────────────────────────────────────────────────────────
function getDB(): AmborDB {
  if (typeof window === 'undefined') return {};
  try {
    return JSON.parse(localStorage.getItem('ambore_db') || '{}');
  } catch {
    return {};
  }
}

function saveDB(d: AmborDB) {
  if (typeof window === 'undefined') return;
  localStorage.setItem('ambore_db', JSON.stringify(d));
}

function getUsers(): AmborDB['users'] {
  return getDB().users || {};
}

function saveUsers(u: AmborDB['users']) {
  const d = getDB();
  d.users = u;
  saveDB(d);
}

// ── Session ────────────────────────────────────────────────────────────────────
export function getSession(): AmborSession | null {
  if (typeof window === 'undefined') return null;
  const d = getDB();
  if (!d.session) return null;
  if (Date.now() > d.session.expires) {
    delete d.session;
    saveDB(d);
    return null;
  }
  return d.session;
}

function saveSession(user: AmborUser) {
  const exp = Date.now() + 7 * 24 * 3600 * 1000; // 7 days
  const d = getDB();
  d.session = { user, expires: exp };
  saveDB(d);
  // Write flat key so all tool pages see the session
  const flat: AmborUserFlat = {
    id: user.email,
    email: user.email,
    name: user.name || user.email,
    picture: user.picture || '',
    expiresAt: exp,
  };
  localStorage.setItem('ambore_user', JSON.stringify(flat));
}

export function clearSession() {
  if (typeof window === 'undefined') return;
  const d = getDB();
  delete d.session;
  saveDB(d);
  localStorage.removeItem('ambore_user');
}

// ── Password hashing (same salt as old site) ───────────────────────────────────
export async function hashPwd(pwd: string): Promise<string> {
  const buf = await crypto.subtle.digest(
    'SHA-256',
    new TextEncoder().encode('ambore2025:' + pwd)
  );
  return Array.from(new Uint8Array(buf))
    .map((b) => b.toString(16).padStart(2, '0'))
    .join('');
}

// ── Email login ────────────────────────────────────────────────────────────────
export async function emailLogin(
  email: string,
  password: string
): Promise<{ ok: true } | { ok: false; error: string }> {
  const em = email.trim().toLowerCase();
  const users = getUsers()!;
  if (!users[em]) return { ok: false, error: 'No account found. Sign up first.' };
  const hash = await hashPwd(password);
  if (users[em].hash !== hash) return { ok: false, error: 'Incorrect password.' };
  saveSession({ email: em, name: users[em].name || em });
  return { ok: true };
}

// ── Email signup ───────────────────────────────────────────────────────────────
export async function emailSignup(
  name: string,
  email: string,
  password: string
): Promise<{ ok: true } | { ok: false; error: string }> {
  const em = email.trim().toLowerCase();
  if (!/^[^@]+@[^@]+\.[^@]+$/.test(em)) return { ok: false, error: 'Invalid email address.' };
  if (password.length < 8) return { ok: false, error: 'Password must be at least 8 characters.' };
  const users = getUsers()!;
  if (users[em]) return { ok: false, error: 'An account with that email already exists.' };
  const hash = await hashPwd(password);
  users[em] = { name: name.trim(), hash, created: Date.now() };
  saveUsers(users);
  saveSession({ email: em, name: name.trim() });
  return { ok: true };
}

// ── Password reset ─────────────────────────────────────────────────────────────
export async function resetPassword(
  email: string,
  newPassword: string
): Promise<{ ok: true } | { ok: false; error: string }> {
  const em = email.trim().toLowerCase();
  const users = getUsers()!;
  if (!users[em]) return { ok: false, error: 'No account found with that email.' };
  if (newPassword.length < 8) return { ok: false, error: 'Password must be at least 8 characters.' };
  users[em].hash = await hashPwd(newPassword);
  saveUsers(users);
  return { ok: true };
}

// ── Google OAuth via Google Identity Services ──────────────────────────────────
declare global {
  interface Window {
    google?: {
      accounts: {
        oauth2: {
          initTokenClient: (config: {
            client_id: string;
            scope: string;
            callback: (resp: { error?: string; access_token?: string }) => void;
          }) => { requestAccessToken: (opts: { prompt: string }) => void };
        };
      };
    };
  }
}

export function googleSignIn(callback: (result: { ok: true; user: AmborUser } | { ok: false; error: string }) => void) {
  if (typeof window === 'undefined' || !window.google?.accounts?.oauth2) {
    callback({ ok: false, error: 'Google sign-in not ready. Try again in a moment.' });
    return;
  }
  const client = window.google.accounts.oauth2.initTokenClient({
    client_id: GOOGLE_CLIENT_ID,
    scope: 'openid email profile',
    callback: (resp: { error?: string; access_token?: string }) => {
      if (resp.error || !resp.access_token) {
        callback({ ok: false, error: 'Google sign-in failed: ' + (resp.error || 'unknown') });
        return;
      }
      fetch('https://www.googleapis.com/oauth2/v3/userinfo', {
        headers: { Authorization: 'Bearer ' + resp.access_token },
      })
        .then((r) => r.json())
        .then((u: { email?: string; name?: string; picture?: string }) => {
          if (!u.email) { callback({ ok: false, error: 'Could not get email from Google.' }); return; }
          const users = getUsers()!;
          if (!users[u.email]) {
            users[u.email] = { name: u.name || u.email, hash: '__google__', created: Date.now() };
            saveUsers(users);
          }
          const user: AmborUser = { email: u.email, name: u.name || u.email, picture: u.picture || '' };
          saveSession(user);
          callback({ ok: true, user });
        })
        .catch(() => callback({ ok: false, error: 'Google sign-in failed. Try again.' }));
    },
  });
  client.requestAccessToken({ prompt: 'select_account' });
}

// Backfill ambore_user from ambore_db for old sessions (keeps tool pages working)
export function backfillAmborUser() {
  if (typeof window === 'undefined') return;
  try {
    const existing = localStorage.getItem('ambore_user');
    if (!existing) {
      const sess = getSession();
      if (sess?.user?.email) {
        localStorage.setItem(
          'ambore_user',
          JSON.stringify({
            id: sess.user.email,
            email: sess.user.email,
            name: sess.user.name || sess.user.email,
            picture: sess.user.picture || '',
            expiresAt: sess.expires,
          })
        );
      }
    }
  } catch {}
}
