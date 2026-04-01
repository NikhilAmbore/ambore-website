'use client';

import { motion } from 'framer-motion';
import Link from 'next/link';
import { ArrowRight, Shield, Clock, CreditCard, Lock } from 'lucide-react';
import Button from '@/components/ui/Button';

const fadeUp = {
  hidden: { opacity: 0, y: 24 },
  visible: (delay: number) => ({
    opacity: 1,
    y: 0,
    transition: { duration: 0.6, delay, ease: [0.25, 0.46, 0.45, 0.94] },
  }),
};

const stats = [
  { value: '12,000+', label: 'users' },
  { value: '87%', label: 'get more interviews' },
  { value: '4.9★', label: 'rated' },
];

const trustBadges = [
  { icon: CreditCard, text: 'No credit card' },
  { icon: Lock, text: 'Free forever' },
  { icon: Shield, text: 'Secure & private' },
  { icon: Clock, text: 'Ready in 60 seconds' },
];

export default function Hero() {
  const scrollToPreview = () => {
    document.getElementById('free-preview')?.scrollIntoView({ behavior: 'smooth' });
  };

  return (
    <section className="relative min-h-screen flex items-center pt-16 overflow-hidden">
      {/* Animated background blobs */}
      <div className="absolute inset-0 overflow-hidden pointer-events-none">
        <div
          className="absolute -top-40 -left-40 w-[600px] h-[600px] rounded-full opacity-20 animate-blob"
          style={{
            background: 'radial-gradient(circle, rgba(249,115,22,0.4) 0%, transparent 70%)',
            filter: 'blur(80px)',
          }}
        />
        <div
          className="absolute -top-20 right-0 w-[500px] h-[500px] rounded-full opacity-15 animate-blob"
          style={{
            background: 'radial-gradient(circle, rgba(37,99,235,0.4) 0%, transparent 70%)',
            filter: 'blur(80px)',
            animationDelay: '2s',
          }}
        />
        <div
          className="absolute bottom-0 left-1/2 -translate-x-1/2 w-[700px] h-[400px] rounded-full opacity-10"
          style={{
            background: 'radial-gradient(circle, rgba(249,115,22,0.3) 0%, transparent 70%)',
            filter: 'blur(100px)',
          }}
        />
        {/* Grid overlay */}
        <div
          className="absolute inset-0 opacity-[0.02]"
          style={{
            backgroundImage:
              'linear-gradient(rgba(255,255,255,0.5) 1px, transparent 1px), linear-gradient(90deg, rgba(255,255,255,0.5) 1px, transparent 1px)',
            backgroundSize: '60px 60px',
          }}
        />
      </div>

      <div className="relative max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-20 text-center">
        {/* Badge */}
        <motion.div
          custom={0}
          variants={fadeUp}
          initial="hidden"
          animate="visible"
          className="inline-flex items-center gap-2 px-3 py-1.5 rounded-full bg-[#F97316]/10 border border-[#F97316]/20 text-[#FB923C] text-sm font-medium mb-8"
        >
          <span className="w-1.5 h-1.5 bg-[#22C55E] rounded-full animate-pulse" />
          Now free for everyone · No signup required to try
        </motion.div>

        {/* Headline */}
        <motion.h1
          custom={0.1}
          variants={fadeUp}
          initial="hidden"
          animate="visible"
          className="text-4xl sm:text-5xl lg:text-6xl xl:text-7xl font-bold text-[#F8FAFC] leading-[1.1] tracking-tight mb-6 max-w-4xl mx-auto"
        >
          Check how well your resume{' '}
          <span
            style={{
              background: 'linear-gradient(135deg, #F97316, #FB923C)',
              WebkitBackgroundClip: 'text',
              WebkitTextFillColor: 'transparent',
              backgroundClip: 'text',
            }}
          >
            matches any job
          </span>{' '}
          — instantly
        </motion.h1>

        {/* Subtext */}
        <motion.p
          custom={0.2}
          variants={fadeUp}
          initial="hidden"
          animate="visible"
          className="text-lg sm:text-xl text-[#94A3B8] max-w-2xl mx-auto mb-10 leading-relaxed"
        >
          Upload your resume + paste a job description → get your{' '}
          <span className="text-[#F8FAFC] font-medium">ATS score</span>,{' '}
          <span className="text-[#F8FAFC] font-medium">missing keywords</span>, and{' '}
          <span className="text-[#F8FAFC] font-medium">optimized resume</span> in 60 seconds.
        </motion.p>

        {/* CTAs */}
        <motion.div
          custom={0.3}
          variants={fadeUp}
          initial="hidden"
          animate="visible"
          className="flex flex-col sm:flex-row items-center justify-center gap-4 mb-12"
        >
          <button
            onClick={scrollToPreview}
            className="inline-flex items-center gap-2 h-12 px-7 bg-[#F97316] hover:bg-[#EA6D09] text-white font-semibold rounded-lg text-base transition-all duration-200 shadow-[0_0_25px_rgba(249,115,22,0.35)] hover:shadow-[0_0_35px_rgba(249,115,22,0.5)] active:scale-[0.98]"
          >
            Check My Resume Score
            <ArrowRight className="w-4.5 h-4.5" style={{ width: '18px', height: '18px' }} />
          </button>
          <Link
            href="/jobs"
            className="inline-flex items-center gap-2 h-12 px-7 bg-white/5 hover:bg-white/10 border border-white/10 hover:border-white/20 text-[#F8FAFC] font-medium rounded-lg text-base transition-all duration-200"
          >
            Browse Jobs
          </Link>
        </motion.div>

        {/* Trust badges */}
        <motion.div
          custom={0.4}
          variants={fadeUp}
          initial="hidden"
          animate="visible"
          className="flex flex-wrap items-center justify-center gap-x-6 gap-y-3 mb-16"
        >
          {trustBadges.map((badge) => (
            <div key={badge.text} className="flex items-center gap-1.5 text-[#94A3B8] text-sm">
              <badge.icon className="w-3.5 h-3.5 text-[#F97316]" />
              <span>{badge.text}</span>
            </div>
          ))}
        </motion.div>

        {/* Stats */}
        <motion.div
          custom={0.5}
          variants={fadeUp}
          initial="hidden"
          animate="visible"
          className="flex flex-wrap items-center justify-center gap-8 sm:gap-16"
        >
          {stats.map((stat, i) => (
            <div key={i} className="text-center">
              <div className="text-3xl sm:text-4xl font-bold text-[#F8FAFC] mb-1">{stat.value}</div>
              <div className="text-sm text-[#94A3B8]">{stat.label}</div>
            </div>
          ))}
        </motion.div>

        {/* Decorative preview card */}
        <motion.div
          custom={0.6}
          variants={fadeUp}
          initial="hidden"
          animate="visible"
          className="mt-20 max-w-3xl mx-auto"
        >
          <div className="bg-white/[0.03] border border-white/[0.08] rounded-2xl p-4 shadow-2xl">
            <div className="flex items-center gap-2 mb-4">
              <div className="w-3 h-3 rounded-full bg-[#EF4444]/60" />
              <div className="w-3 h-3 rounded-full bg-[#F59E0B]/60" />
              <div className="w-3 h-3 rounded-full bg-[#22C55E]/60" />
              <div className="flex-1 h-5 bg-white/5 rounded ml-2 max-w-xs" />
            </div>
            <div className="grid grid-cols-3 gap-4">
              <div className="col-span-2 space-y-2">
                <div className="h-4 bg-white/5 rounded w-3/4" />
                <div className="h-4 bg-white/5 rounded w-full" />
                <div className="h-4 bg-white/5 rounded w-5/6" />
                <div className="h-4 bg-white/5 rounded w-2/3" />
                <div className="h-4 bg-white/5 rounded w-4/5" />
              </div>
              <div className="flex flex-col items-center justify-center gap-3">
                <div className="relative w-20 h-20">
                  <svg className="w-20 h-20 -rotate-90" viewBox="0 0 80 80">
                    <circle cx="40" cy="40" r="33" fill="none" stroke="rgba(255,255,255,0.06)" strokeWidth="6" />
                    <circle
                      cx="40"
                      cy="40"
                      r="33"
                      fill="none"
                      stroke="#F97316"
                      strokeWidth="6"
                      strokeDasharray={`${2 * Math.PI * 33}`}
                      strokeDashoffset={`${2 * Math.PI * 33 * (1 - 0.78)}`}
                      strokeLinecap="round"
                    />
                  </svg>
                  <div className="absolute inset-0 flex flex-col items-center justify-center">
                    <span className="text-xl font-bold text-[#F8FAFC]">78</span>
                    <span className="text-[10px] text-[#94A3B8]">score</span>
                  </div>
                </div>
                <div className="text-xs text-[#22C55E] font-medium bg-[#22C55E]/10 px-2 py-0.5 rounded-full">
                  Good Match
                </div>
              </div>
            </div>
          </div>
        </motion.div>
      </div>
    </section>
  );
}
