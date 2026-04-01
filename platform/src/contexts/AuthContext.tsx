'use client';

import React, { createContext, useContext, useEffect, useState, useCallback } from 'react';
import {
  getSession,
  clearSession,
  backfillAmborUser,
  type AmborSession,
  type AmborUser,
} from '@/lib/auth-client';

interface AuthContextValue {
  session: AmborSession | null;
  user: AmborUser | null;
  loading: boolean;
  refresh: () => void;
  logout: () => void;
}

const AuthContext = createContext<AuthContextValue>({
  session: null,
  user: null,
  loading: true,
  refresh: () => {},
  logout: () => {},
});

export function AuthProvider({ children }: { children: React.ReactNode }) {
  const [session, setSession] = useState<AmborSession | null>(null);
  const [loading, setLoading] = useState(true);

  const refresh = useCallback(() => {
    backfillAmborUser();
    const s = getSession();
    setSession(s);
    setLoading(false);
  }, []);

  const logout = useCallback(() => {
    clearSession();
    setSession(null);
  }, []);

  useEffect(() => {
    refresh();
    // Re-check on tab focus (cross-tab logout support)
    const onFocus = () => refresh();
    window.addEventListener('focus', onFocus);
    return () => window.removeEventListener('focus', onFocus);
  }, [refresh]);

  return (
    <AuthContext.Provider value={{ session, user: session?.user ?? null, loading, refresh, logout }}>
      {children}
    </AuthContext.Provider>
  );
}

export function useAuthContext() {
  return useContext(AuthContext);
}
