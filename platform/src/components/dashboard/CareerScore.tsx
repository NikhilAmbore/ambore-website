'use client';

import { motion } from 'framer-motion';
import { TrendingUp, FileText, Target, MessageSquare } from 'lucide-react';
import type { CareerScore as CareerScoreType } from '@/types';
import { scoreColor, getScoreLabel } from '@/lib/utils';
import Link from 'next/link';

interface CareerScoreProps {
  score: CareerScoreType | null;
}

const subScores = [
  {
    key: 'resumeScore' as keyof CareerScoreType,
    label: 'Resume Score',
    icon: FileText,
    href: '/resume',
    color: '#2563EB',
  },
  {
    key: 'atsScore' as keyof CareerScoreType,
    label: 'ATS Score',
    icon: Target,
    href: '/resume',
    color: '#F97316',
  },
  {
    key: 'interviewScore' as keyof CareerScoreType,
    label: 'Interview Prep',
    icon: MessageSquare,
    href: '/interview',
    color: '#22C55E',
  },
];

export default function CareerScore({ score }: CareerScoreProps) {
  const overall = score?.overall ?? 0;
  const circumference = 2 * Math.PI * 54;
  const color = scoreColor(overall);
  const label = getScoreLabel(overall);

  return (
    <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-6">
      <div className="flex items-center gap-2 mb-6">
        <TrendingUp className="w-5 h-5 text-[#F97316]" />
        <h2 className="text-base font-semibold text-[#F8FAFC]">Career Score</h2>
      </div>

      <div className="flex flex-col sm:flex-row items-center gap-8">
        {/* Circular Score Ring */}
        <div className="relative w-36 h-36 shrink-0">
          <svg className="w-36 h-36 -rotate-90" viewBox="0 0 128 128">
            <circle
              cx="64"
              cy="64"
              r="54"
              fill="none"
              stroke="rgba(255,255,255,0.06)"
              strokeWidth="10"
            />
            <motion.circle
              cx="64"
              cy="64"
              r="54"
              fill="none"
              stroke={color}
              strokeWidth="10"
              strokeLinecap="round"
              strokeDasharray={circumference}
              initial={{ strokeDashoffset: circumference }}
              animate={{
                strokeDashoffset: circumference * (1 - overall / 100),
              }}
              transition={{ duration: 1.5, ease: 'easeOut', delay: 0.2 }}
              style={{ filter: `drop-shadow(0 0 8px ${color}60)` }}
            />
          </svg>
          <div className="absolute inset-0 flex flex-col items-center justify-center">
            <motion.span
              className="text-4xl font-bold text-[#F8FAFC] leading-none"
              initial={{ opacity: 0, scale: 0.8 }}
              animate={{ opacity: 1, scale: 1 }}
              transition={{ duration: 0.5, delay: 0.8 }}
            >
              {overall}
            </motion.span>
            <span className="text-xs text-[#94A3B8] mt-1">out of 100</span>
            <span
              className="text-xs font-semibold mt-0.5"
              style={{ color }}
            >
              {label}
            </span>
          </div>
        </div>

        {/* Sub Scores */}
        <div className="flex-1 w-full space-y-4">
          {subScores.map((item, index) => {
            const Icon = item.icon;
            const value = (score?.[item.key] as number) ?? 0;
            const barColor = scoreColor(value);

            return (
              <motion.div
                key={item.key}
                initial={{ opacity: 0, x: 20 }}
                animate={{ opacity: 1, x: 0 }}
                transition={{ duration: 0.5, delay: 0.3 + index * 0.1 }}
              >
                <div className="flex items-center justify-between mb-1.5">
                  <div className="flex items-center gap-2">
                    <Icon className="w-3.5 h-3.5" style={{ color: item.color }} />
                    <span className="text-sm text-[#CBD5E1]">{item.label}</span>
                  </div>
                  <div className="flex items-center gap-2">
                    <span className="text-sm font-semibold text-[#F8FAFC]">{value}</span>
                    <Link
                      href={item.href}
                      className="text-xs text-[#F97316] hover:text-[#FB923C] transition-colors"
                    >
                      Improve →
                    </Link>
                  </div>
                </div>
                <div className="h-2 bg-white/[0.06] rounded-full overflow-hidden">
                  <motion.div
                    className="h-full rounded-full"
                    style={{ backgroundColor: barColor }}
                    initial={{ width: 0 }}
                    animate={{ width: `${value}%` }}
                    transition={{ duration: 1, delay: 0.5 + index * 0.1, ease: 'easeOut' }}
                  />
                </div>
              </motion.div>
            );
          })}
        </div>
      </div>

      {/* CTA row */}
      <div className="mt-6 pt-5 border-t border-white/[0.06] flex flex-wrap gap-3">
        <Link
          href="/resume"
          className="flex-1 min-w-[120px] h-9 bg-[#F97316]/10 hover:bg-[#F97316]/20 border border-[#F97316]/20 hover:border-[#F97316]/30 rounded-lg text-sm font-medium text-[#FB923C] flex items-center justify-center transition-all"
        >
          Analyze Resume
        </Link>
        <Link
          href="/interview"
          className="flex-1 min-w-[120px] h-9 bg-white/[0.05] hover:bg-white/[0.08] border border-white/10 rounded-lg text-sm font-medium text-[#CBD5E1] flex items-center justify-center transition-all"
        >
          Practice Interview
        </Link>
      </div>
    </div>
  );
}
