'use client';

export const dynamic = 'force-dynamic';

import { Suspense, useState } from 'react';
import Link from 'next/link';
import { useRouter, useSearchParams } from 'next/navigation';
import { signIn } from 'next-auth/react';
import { motion } from 'framer-motion';
import { Eye, EyeOff, Zap, Mail, Lock } from 'lucide-react';
import toast from 'react-hot-toast';

const errorMessages: Record<string, string> = {
  OAuthSignin: 'Error starting OAuth sign in. Please try again.',
  OAuthCallback: 'Error during OAuth callback. Please try again.',
  OAuthCreateAccount: 'Could not create OAuth account. Email may already be in use.',
  EmailCreateAccount: 'Could not create email account.',
  Callback: 'Error during sign in callback.',
  OAuthAccountNotLinked: 'This email is already linked to a different sign in method.',
  CredentialsSignin: 'Invalid email or password.',
  Default: 'An error occurred. Please try again.',
};

function SignInForm() {
  const router = useRouter();
  const searchParams = useSearchParams();
  const callbackUrl = searchParams.get('callbackUrl') ?? '/dashboard';
  const error = searchParams.get('error');
  const errorMessage = error ? (errorMessages[error] ?? errorMessages.Default) : null;

  const [email, setEmail] = useState('');
  const [password, setPassword] = useState('');
  const [showPassword, setShowPassword] = useState(false);
  const [loading, setLoading] = useState(false);
  const [googleLoading, setGoogleLoading] = useState(false);

  const handleGoogleSignIn = async () => {
    setGoogleLoading(true);
    try {
      await signIn('google', { callbackUrl });
    } catch {
      toast.error('Failed to sign in with Google');
      setGoogleLoading(false);
    }
  };

  const handleCredentialsSignIn = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!email || !password) {
      toast.error('Please enter your email and password');
      return;
    }
    setLoading(true);
    try {
      const result = await signIn('credentials', { email, password, redirect: false, callbackUrl });
      if (result?.error) {
        toast.error(errorMessages.CredentialsSignin);
      } else if (result?.ok) {
        toast.success('Welcome back!');
        router.push(callbackUrl);
      }
    } catch {
      toast.error('Sign in failed. Please try again.');
    } finally {
      setLoading(false);
    }
  };

  return (
    <div className="bg-white/[0.04] border border-white/[0.08] rounded-2xl p-8">
      <div className="mb-6 text-center">
        <h1 className="text-2xl font-bold text-[#F8FAFC] mb-1">Welcome back</h1>
        <p className="text-sm text-[#94A3B8]">Sign in to your account to continue</p>
      </div>

      {errorMessage && (
        <div className="mb-4 p-3 bg-[#EF4444]/10 border border-[#EF4444]/20 rounded-lg text-sm text-[#F87171]">
          {errorMessage}
        </div>
      )}

      <button
        onClick={handleGoogleSignIn}
        disabled={googleLoading || loading}
        className="w-full h-11 flex items-center justify-center gap-3 bg-white/[0.07] hover:bg-white/[0.11] border border-white/[0.12] hover:border-white/[0.2] rounded-lg text-sm font-medium text-[#F8FAFC] transition-all mb-4 disabled:opacity-50 disabled:cursor-not-allowed"
      >
        {googleLoading ? (
          <div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" />
        ) : (
          <svg className="w-4 h-4" viewBox="0 0 24 24">
            <path fill="#4285F4" d="M22.56 12.25c0-.78-.07-1.53-.2-2.25H12v4.26h5.92c-.26 1.37-1.04 2.53-2.21 3.31v2.77h3.57c2.08-1.92 3.28-4.74 3.28-8.09z" />
            <path fill="#34A853" d="M12 23c2.97 0 5.46-.98 7.28-2.66l-3.57-2.77c-.98.66-2.23 1.06-3.71 1.06-2.86 0-5.29-1.93-6.16-4.53H2.18v2.84C3.99 20.53 7.7 23 12 23z" />
            <path fill="#FBBC05" d="M5.84 14.09c-.22-.66-.35-1.36-.35-2.09s.13-1.43.35-2.09V7.07H2.18C1.43 8.55 1 10.22 1 12s.43 3.45 1.18 4.93l2.85-2.22.81-.62z" />
            <path fill="#EA4335" d="M12 5.38c1.62 0 3.06.56 4.21 1.64l3.15-3.15C17.45 2.09 14.97 1 12 1 7.7 1 3.99 3.47 2.18 7.07l3.66 2.84c.87-2.6 3.3-4.53 6.16-4.53z" />
          </svg>
        )}
        Continue with Google
      </button>

      <div className="divider mb-4">or continue with email</div>

      <form onSubmit={handleCredentialsSignIn} className="space-y-4">
        <div className="space-y-1.5">
          <label className="block text-sm font-medium text-[#CBD5E1]">Email</label>
          <div className="relative">
            <Mail className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-[#94A3B8]" />
            <input
              type="email"
              value={email}
              onChange={e => setEmail(e.target.value)}
              placeholder="you@example.com"
              required
              className="w-full h-10 pl-10 pr-4 bg-white/[0.04] border border-white/10 rounded-lg text-sm text-[#F8FAFC] placeholder:text-[#475569] focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
            />
          </div>
        </div>

        <div className="space-y-1.5">
          <div className="flex items-center justify-between">
            <label className="text-sm font-medium text-[#CBD5E1]">Password</label>
            <Link href="/auth/forgot-password" className="text-xs text-[#F97316] hover:text-[#FB923C] transition-colors">
              Forgot password?
            </Link>
          </div>
          <div className="relative">
            <Lock className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-[#94A3B8]" />
            <input
              type={showPassword ? 'text' : 'password'}
              value={password}
              onChange={e => setPassword(e.target.value)}
              placeholder="Enter your password"
              required
              className="w-full h-10 pl-10 pr-10 bg-white/[0.04] border border-white/10 rounded-lg text-sm text-[#F8FAFC] placeholder:text-[#475569] focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
            />
            <button
              type="button"
              onClick={() => setShowPassword(!showPassword)}
              className="absolute right-3 top-1/2 -translate-y-1/2 text-[#94A3B8] hover:text-white transition-colors"
            >
              {showPassword ? <EyeOff className="w-4 h-4" /> : <Eye className="w-4 h-4" />}
            </button>
          </div>
        </div>

        <button
          type="submit"
          disabled={loading || googleLoading}
          className="w-full h-11 bg-[#F97316] hover:bg-[#EA6D09] disabled:opacity-50 disabled:cursor-not-allowed text-white font-semibold rounded-lg text-sm transition-all shadow-[0_0_20px_rgba(249,115,22,0.3)] hover:shadow-[0_0_30px_rgba(249,115,22,0.5)] flex items-center justify-center gap-2"
        >
          {loading && <div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" />}
          Sign In
        </button>
      </form>

      <p className="mt-6 text-center text-sm text-[#94A3B8]">
        Don&rsquo;t have an account?{' '}
        <Link href="/auth/signup" className="text-[#F97316] hover:text-[#FB923C] font-medium transition-colors">
          Create one free
        </Link>
      </p>
    </div>
  );
}

export default function SignInPage() {
  return (
    <div className="min-h-screen bg-[#09090B] flex flex-col items-center justify-center px-4 py-12">
      <div className="absolute inset-0 overflow-hidden pointer-events-none">
        <div
          className="absolute top-0 right-0 w-[500px] h-[500px] opacity-10"
          style={{ background: 'radial-gradient(circle, rgba(249,115,22,0.4) 0%, transparent 70%)', filter: 'blur(80px)' }}
        />
      </div>
      <motion.div
        initial={{ opacity: 0, y: 20 }}
        animate={{ opacity: 1, y: 0 }}
        transition={{ duration: 0.5 }}
        className="relative w-full max-w-md"
      >
        <Link href="/" className="flex items-center justify-center gap-2 mb-8">
          <div className="w-9 h-9 bg-[#F97316] rounded-lg flex items-center justify-center shadow-[0_0_20px_rgba(249,115,22,0.4)]">
            <Zap className="w-5 h-5 text-white" />
          </div>
          <span className="font-bold text-xl text-[#F8FAFC]">Ambore</span>
        </Link>
        <Suspense fallback={<div className="h-96 bg-white/[0.04] border border-white/[0.08] rounded-2xl animate-pulse" />}>
          <SignInForm />
        </Suspense>
      </motion.div>
    </div>
  );
}
