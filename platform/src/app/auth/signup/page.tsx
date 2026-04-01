'use client';

export const dynamic = 'force-dynamic';

import { useState } from 'react';
import Link from 'next/link';
import { useRouter } from 'next/navigation';
import { signIn } from 'next-auth/react';
import { motion } from 'framer-motion';
import { Eye, EyeOff, Zap, Mail, Lock, User, Shield } from 'lucide-react';
import toast from 'react-hot-toast';

export default function SignUpPage() {
  const router = useRouter();

  const [name, setName] = useState('');
  const [email, setEmail] = useState('');
  const [password, setPassword] = useState('');
  const [showPassword, setShowPassword] = useState(false);
  const [loading, setLoading] = useState(false);
  const [googleLoading, setGoogleLoading] = useState(false);

  const handleGoogleSignUp = async () => {
    setGoogleLoading(true);
    try {
      await signIn('google', { callbackUrl: '/dashboard' });
    } catch {
      toast.error('Failed to sign up with Google');
      setGoogleLoading(false);
    }
  };

  const handleSignUp = async (e: React.FormEvent) => {
    e.preventDefault();

    if (!name.trim()) {
      toast.error('Please enter your name');
      return;
    }
    if (!email.trim()) {
      toast.error('Please enter your email');
      return;
    }
    if (password.length < 8) {
      toast.error('Password must be at least 8 characters');
      return;
    }

    setLoading(true);
    try {
      const response = await fetch('/api/auth/register', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ name, email, password }),
      });

      const data = await response.json();

      if (!response.ok) {
        throw new Error(data.error ?? 'Registration failed');
      }

      // Sign in after successful registration
      const result = await signIn('credentials', {
        email,
        password,
        redirect: false,
        callbackUrl: '/dashboard',
      });

      if (result?.ok) {
        toast.success('Account created! Welcome to Ambore!');
        router.push('/dashboard');
      } else {
        toast.success('Account created! Please sign in.');
        router.push('/auth/signin');
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Registration failed';
      toast.error(message);
    } finally {
      setLoading(false);
    }
  };

  const passwordStrength = (): { score: number; label: string; color: string } => {
    if (password.length === 0) return { score: 0, label: '', color: '' };
    let score = 0;
    if (password.length >= 8) score++;
    if (password.length >= 12) score++;
    if (/[A-Z]/.test(password)) score++;
    if (/[0-9]/.test(password)) score++;
    if (/[^A-Za-z0-9]/.test(password)) score++;

    if (score <= 1) return { score: 20, label: 'Weak', color: '#EF4444' };
    if (score <= 2) return { score: 40, label: 'Fair', color: '#F59E0B' };
    if (score <= 3) return { score: 70, label: 'Good', color: '#22C55E' };
    return { score: 100, label: 'Strong', color: '#22C55E' };
  };

  const strength = passwordStrength();

  return (
    <div className="min-h-screen bg-[#09090B] flex flex-col items-center justify-center px-4 py-12">
      {/* Background */}
      <div className="absolute inset-0 overflow-hidden pointer-events-none">
        <div
          className="absolute top-0 left-0 w-[500px] h-[500px] opacity-10"
          style={{
            background: 'radial-gradient(circle, rgba(37,99,235,0.4) 0%, transparent 70%)',
            filter: 'blur(80px)',
          }}
        />
      </div>

      <motion.div
        initial={{ opacity: 0, y: 20 }}
        animate={{ opacity: 1, y: 0 }}
        transition={{ duration: 0.5 }}
        className="relative w-full max-w-md"
      >
        {/* Logo */}
        <Link href="/" className="flex items-center justify-center gap-2 mb-8">
          <div className="w-9 h-9 bg-[#F97316] rounded-lg flex items-center justify-center shadow-[0_0_20px_rgba(249,115,22,0.4)]">
            <Zap className="w-5 h-5 text-white" />
          </div>
          <span className="font-bold text-xl text-[#F8FAFC]">Ambore</span>
        </Link>

        <div className="bg-white/[0.04] border border-white/[0.08] rounded-2xl p-8">
          <div className="mb-6 text-center">
            <h1 className="text-2xl font-bold text-[#F8FAFC] mb-1">Create your account</h1>
            <p className="text-sm text-[#94A3B8]">
              No credit card required · Takes 30 seconds
            </p>
          </div>

          {/* Google Sign Up */}
          <button
            onClick={handleGoogleSignUp}
            disabled={googleLoading || loading}
            className="w-full h-11 flex items-center justify-center gap-3 bg-white/[0.07] hover:bg-white/[0.11] border border-white/[0.12] hover:border-white/[0.2] rounded-lg text-sm font-medium text-[#F8FAFC] transition-all mb-4 disabled:opacity-50 disabled:cursor-not-allowed"
          >
            {googleLoading ? (
              <div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" />
            ) : (
              <svg className="w-4 h-4" viewBox="0 0 24 24">
                <path
                  fill="#4285F4"
                  d="M22.56 12.25c0-.78-.07-1.53-.2-2.25H12v4.26h5.92c-.26 1.37-1.04 2.53-2.21 3.31v2.77h3.57c2.08-1.92 3.28-4.74 3.28-8.09z"
                />
                <path
                  fill="#34A853"
                  d="M12 23c2.97 0 5.46-.98 7.28-2.66l-3.57-2.77c-.98.66-2.23 1.06-3.71 1.06-2.86 0-5.29-1.93-6.16-4.53H2.18v2.84C3.99 20.53 7.7 23 12 23z"
                />
                <path
                  fill="#FBBC05"
                  d="M5.84 14.09c-.22-.66-.35-1.36-.35-2.09s.13-1.43.35-2.09V7.07H2.18C1.43 8.55 1 10.22 1 12s.43 3.45 1.18 4.93l2.85-2.22.81-.62z"
                />
                <path
                  fill="#EA4335"
                  d="M12 5.38c1.62 0 3.06.56 4.21 1.64l3.15-3.15C17.45 2.09 14.97 1 12 1 7.7 1 3.99 3.47 2.18 7.07l3.66 2.84c.87-2.6 3.3-4.53 6.16-4.53z"
                />
              </svg>
            )}
            Continue with Google
          </button>

          {/* Divider */}
          <div className="divider mb-4">or sign up with email</div>

          {/* Registration Form */}
          <form onSubmit={handleSignUp} className="space-y-4">
            <div className="space-y-1.5">
              <label className="block text-sm font-medium text-[#CBD5E1]">Full Name</label>
              <div className="relative">
                <User className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-[#94A3B8]" />
                <input
                  type="text"
                  value={name}
                  onChange={(e) => setName(e.target.value)}
                  placeholder="Jane Smith"
                  required
                  className="w-full h-10 pl-10 pr-4 bg-white/[0.04] border border-white/10 rounded-lg text-sm text-[#F8FAFC] placeholder:text-[#475569] focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
                />
              </div>
            </div>

            <div className="space-y-1.5">
              <label className="block text-sm font-medium text-[#CBD5E1]">Email</label>
              <div className="relative">
                <Mail className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-[#94A3B8]" />
                <input
                  type="email"
                  value={email}
                  onChange={(e) => setEmail(e.target.value)}
                  placeholder="you@example.com"
                  required
                  className="w-full h-10 pl-10 pr-4 bg-white/[0.04] border border-white/10 rounded-lg text-sm text-[#F8FAFC] placeholder:text-[#475569] focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
                />
              </div>
            </div>

            <div className="space-y-1.5">
              <label className="block text-sm font-medium text-[#CBD5E1]">Password</label>
              <div className="relative">
                <Lock className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-[#94A3B8]" />
                <input
                  type={showPassword ? 'text' : 'password'}
                  value={password}
                  onChange={(e) => setPassword(e.target.value)}
                  placeholder="Minimum 8 characters"
                  required
                  minLength={8}
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

              {/* Password strength */}
              {password.length > 0 && (
                <div className="mt-2 space-y-1">
                  <div className="h-1 bg-white/10 rounded-full overflow-hidden">
                    <div
                      className="h-full rounded-full transition-all duration-300"
                      style={{ width: `${strength.score}%`, backgroundColor: strength.color }}
                    />
                  </div>
                  <p className="text-xs" style={{ color: strength.color }}>
                    Password strength: {strength.label}
                  </p>
                </div>
              )}
            </div>

            <button
              type="submit"
              disabled={loading || googleLoading}
              className="w-full h-11 bg-[#F97316] hover:bg-[#EA6D09] disabled:opacity-50 disabled:cursor-not-allowed text-white font-semibold rounded-lg text-sm transition-all shadow-[0_0_20px_rgba(249,115,22,0.3)] hover:shadow-[0_0_30px_rgba(249,115,22,0.5)] flex items-center justify-center gap-2"
            >
              {loading && (
                <div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" />
              )}
              Create Free Account
            </button>
          </form>

          {/* Privacy note */}
          <div className="mt-4 flex items-center justify-center gap-2 text-xs text-[#94A3B8]">
            <Shield className="w-3 h-3 shrink-0" />
            <span>We never sell your data. Ever.</span>
          </div>

          <p className="mt-4 text-center text-sm text-[#94A3B8]">
            Already have an account?{' '}
            <Link href="/auth/signin" className="text-[#F97316] hover:text-[#FB923C] font-medium transition-colors">
              Sign in
            </Link>
          </p>

          <p className="mt-3 text-center text-xs text-[#475569]">
            By signing up, you agree to our{' '}
            <Link href="/terms" className="hover:text-[#94A3B8] transition-colors underline">
              Terms of Service
            </Link>{' '}
            and{' '}
            <Link href="/privacy" className="hover:text-[#94A3B8] transition-colors underline">
              Privacy Policy
            </Link>
            .
          </p>
        </div>
      </motion.div>
    </div>
  );
}
