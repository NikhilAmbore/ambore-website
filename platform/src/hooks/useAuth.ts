'use client';

import { useAuthContext } from '@/contexts/AuthContext';

export function useAuth() {
  const { session, user, loading, refresh, logout } = useAuthContext();
  return {
    session,
    user,
    loading,
    isLoggedIn: !!session,
    isAuthenticated: !!session,
    isLoading: loading,
    refresh,
    logout,
  };
}

export default useAuth;
