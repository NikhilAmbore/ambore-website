'use client';

import { useState } from 'react';
import Link from 'next/link';
import { Zap, Mail, ArrowLeft, CheckCircle } from 'lucide-react';
import toast from 'react-hot-toast';

export default function ForgotPasswordPage() {
  const [email, setEmail] = useState('');
  const [loading, setLoading] = useState(false);
  const [sent, setSent] = useState(false);

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!email.trim()) {
      toast.error('Please enter your email address');
      return;
    }
    setLoading(true);
    try {
      // In production, call /api/auth/forgot-password
      // For now show success to prevent email enumeration
      await new Promise(r => setTimeout(r, 800));
      setSent(true);
    } catch {
      toast.error('Something went wrong. Please try again.');
    } finally {
      setLoading(false);
    }
  };

  return (
    <div className="min-h-screen bg-[#09090B] flex flex-col items-center justify-center px-4 py-12">
      <div className="absolute inset-0 overflow-hidden pointer-events-none">
        <div
          className="absolute top-0 right-0 w-[400px] h-[400px] opacity-10"
          style={{ background: 'radial-gradient(circle, rgba(249,115,22,0.4) 0%, transparent 70%)', filter: 'blur(80px)' }}
        />
      </div>

      <div className="relative w-full max-w-md">
        <Link href="/" className="flex items-center justify-center gap-2 mb-8">
          <div className="w-9 h-9 bg-[#F97316] rounded-lg flex items-center justify-center shadow-[0_0_20px_rgba(249,115,22,0.4)]">
            <Zap className="w-5 h-5 text-white" />
          </div>
          <span className="font-bold text-xl text-[#F8FAFC]">Ambore</span>
        </Link>

        <div className="bg-white/[0.04] border border-white/[0.08] rounded-2xl p-8">
          {sent ? (
            <div className="text-center">
              <CheckCircle className="w-12 h-12 text-[#22C55E] mx-auto mb-4" />
              <h1 className="text-xl font-bold text-[#F8FAFC] mb-2">Check your email</h1>
              <p className="text-sm text-[#94A3B8] mb-6">
                If an account exists for <span className="text-[#F8FAFC]">{email}</span>, you&apos;ll receive a password reset link shortly.
              </p>
              <Link
                href="/auth/signin"
                className="flex items-center justify-center gap-2 text-sm text-[#F97316] hover:text-[#FB923C] transition-colors"
              >
                <ArrowLeft className="w-4 h-4" /> Back to sign in
              </Link>
            </div>
          ) : (
            <>
              <div className="mb-6">
                <h1 className="text-2xl font-bold text-[#F8FAFC] mb-1">Reset password</h1>
                <p className="text-sm text-[#94A3B8]">Enter your email and we&apos;ll send you a reset link.</p>
              </div>

              <form onSubmit={handleSubmit} className="space-y-4">
                <div className="space-y-1.5">
                  <label className="block text-sm font-medium text-[#CBD5E1]">Email address</label>
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

                <button
                  type="submit"
                  disabled={loading}
                  className="w-full h-11 bg-[#F97316] hover:bg-[#EA6D09] disabled:opacity-50 disabled:cursor-not-allowed text-white font-semibold rounded-lg text-sm transition-all flex items-center justify-center gap-2"
                >
                  {loading && <div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" />}
                  Send Reset Link
                </button>
              </form>

              <div className="mt-6 text-center">
                <Link
                  href="/auth/signin"
                  className="flex items-center justify-center gap-1.5 text-sm text-[#94A3B8] hover:text-[#F8FAFC] transition-colors"
                >
                  <ArrowLeft className="w-3.5 h-3.5" /> Back to sign in
                </Link>
              </div>
            </>
          )}
        </div>
      </div>
    </div>
  );
}
