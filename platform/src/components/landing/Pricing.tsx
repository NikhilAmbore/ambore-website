'use client';

import { motion } from 'framer-motion';
import { Check, Zap } from 'lucide-react';
import Link from 'next/link';

const freeFeatures = [
  'Unlimited resume analyses',
  'ATS compatibility score',
  'Missing keywords detection',
  '5 improvement suggestions per analysis',
  'Job description matching',
  'Format quality score',
  'Save up to 3 resumes',
  'Access to job listings',
];

const proFeatures = [
  'Everything in Free',
  'GPT-4o powered deep analysis',
  'Unlimited saved resumes',
  'Improved bullet point rewrites',
  'Interview question generator',
  'Career score tracking',
  'Priority processing',
  'Email support',
];

export default function Pricing() {
  const handleWaitlist = () => {
    if (typeof window !== 'undefined' && (window as unknown as { posthog?: { capture: (event: string) => void } }).posthog) {
      (window as unknown as { posthog: { capture: (event: string) => void } }).posthog.capture('pro_waitlist_clicked');
    }
    window.open('mailto:hello@ambore.io?subject=Pro Waitlist', '_blank');
  };

  return (
    <section id="pricing" className="py-24 relative overflow-hidden">
      {/* Background */}
      <div className="absolute inset-0 pointer-events-none">
        <div
          className="absolute top-1/2 left-1/2 -translate-x-1/2 -translate-y-1/2 w-[800px] h-[600px] opacity-[0.06]"
          style={{
            background: 'radial-gradient(ellipse, rgba(249,115,22,0.8) 0%, transparent 70%)',
            filter: 'blur(80px)',
          }}
        />
      </div>

      <div className="relative max-w-5xl mx-auto px-4 sm:px-6 lg:px-8">
        {/* Header */}
        <div className="text-center mb-16">
          <motion.p
            initial={{ opacity: 0, y: 10 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ duration: 0.5 }}
            className="text-sm font-medium text-[#F97316] uppercase tracking-widest mb-3"
          >
            Pricing
          </motion.p>
          <motion.h2
            initial={{ opacity: 0, y: 15 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ duration: 0.5, delay: 0.1 }}
            className="text-3xl sm:text-4xl font-bold text-[#F8FAFC] mb-4"
          >
            Simple, honest pricing
          </motion.h2>
          <motion.p
            initial={{ opacity: 0, y: 15 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ duration: 0.5, delay: 0.2 }}
            className="text-[#94A3B8] text-lg"
          >
            Start free. Upgrade when you&rsquo;re ready.
          </motion.p>
        </div>

        {/* Cards */}
        <div className="grid grid-cols-1 md:grid-cols-2 gap-8 max-w-3xl mx-auto">
          {/* Free Plan */}
          <motion.div
            initial={{ opacity: 0, x: -30 }}
            whileInView={{ opacity: 1, x: 0 }}
            viewport={{ once: true }}
            transition={{ duration: 0.6 }}
            whileHover={{ y: -4, transition: { duration: 0.2 } }}
            className="bg-white/[0.04] border border-white/[0.08] rounded-2xl p-8 flex flex-col hover:border-white/[0.15] transition-all"
          >
            <div className="mb-6">
              <h3 className="text-xl font-bold text-[#F8FAFC] mb-1">Free</h3>
              <div className="flex items-end gap-1 mb-3">
                <span className="text-4xl font-bold text-[#F8FAFC]">$0</span>
                <span className="text-[#94A3B8] mb-1.5">/month</span>
              </div>
              <p className="text-sm text-[#94A3B8]">Everything you need to land your next job.</p>
            </div>

            <ul className="space-y-3 flex-1 mb-8">
              {freeFeatures.map((feature) => (
                <li key={feature} className="flex items-center gap-3 text-sm text-[#CBD5E1]">
                  <Check className="w-4 h-4 text-[#22C55E] shrink-0" />
                  {feature}
                </li>
              ))}
            </ul>

            <Link href="/auth/signup"
              className="block w-full h-11 bg-white/10 hover:bg-white/15 border border-white/15 hover:border-white/25 text-[#F8FAFC] font-semibold rounded-lg text-sm transition-all flex items-center justify-center">
              Get Started Free
            </Link>
          </motion.div>

          {/* Pro Plan */}
          <motion.div
            initial={{ opacity: 0, x: 30 }}
            whileInView={{ opacity: 1, x: 0 }}
            viewport={{ once: true }}
            transition={{ duration: 0.6, delay: 0.1 }}
            whileHover={{ y: -4, transition: { duration: 0.2 } }}
            className="relative bg-gradient-to-b from-[#F97316]/10 to-white/[0.03] border border-[#F97316]/30 rounded-2xl p-8 flex flex-col hover:border-[#F97316]/50 transition-all"
          >
            {/* Popular badge */}
            <div className="absolute -top-3 left-1/2 -translate-x-1/2">
              <div className="flex items-center gap-1.5 px-3 py-1 bg-[#F97316] rounded-full shadow-[0_0_20px_rgba(249,115,22,0.4)]">
                <Zap className="w-3 h-3 text-white" />
                <span className="text-xs font-bold text-white">Coming Soon</span>
              </div>
            </div>

            <div className="mb-6">
              <h3 className="text-xl font-bold text-[#F8FAFC] mb-1">Pro</h3>
              <div className="flex items-end gap-1 mb-3">
                <span className="text-4xl font-bold text-[#F8FAFC]">$9</span>
                <span className="text-[#94A3B8] mb-1.5">/month</span>
              </div>
              <p className="text-sm text-[#94A3B8]">For serious job seekers who want every edge.</p>
            </div>

            <ul className="space-y-3 flex-1 mb-8">
              {proFeatures.map((feature) => (
                <li key={feature} className="flex items-center gap-3 text-sm text-[#CBD5E1]">
                  <Check className="w-4 h-4 text-[#F97316] shrink-0" />
                  {feature}
                </li>
              ))}
            </ul>

            <button
              onClick={handleWaitlist}
              className="w-full h-11 bg-[#F97316] hover:bg-[#EA6D09] text-white font-semibold rounded-lg text-sm transition-all shadow-[0_0_20px_rgba(249,115,22,0.3)] hover:shadow-[0_0_30px_rgba(249,115,22,0.5)]"
            >
              Join Waitlist
            </button>
            <p className="text-center text-xs text-[#94A3B8] mt-2">
              Be first to know when Pro launches
            </p>
          </motion.div>
        </div>

        {/* Bottom note */}
        <motion.p
          initial={{ opacity: 0 }}
          whileInView={{ opacity: 1 }}
          viewport={{ once: true }}
          transition={{ duration: 0.5, delay: 0.4 }}
          className="text-center text-[#94A3B8] text-sm mt-10"
        >
          No credit card required. Cancel anytime. 🔒 We never sell your data.
        </motion.p>
      </div>
    </section>
  );
}
