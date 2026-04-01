'use client';

import { motion } from 'framer-motion';
import { FileText, Target, Send, TrendingUp } from 'lucide-react';

interface StatsGridProps {
  resumeCount: number;
  savedJobsCount: number;
  atsScore: number;
  scoreImprovement: number;
}

const stats = (data: StatsGridProps) => [
  {
    label: 'Resumes Saved',
    value: data.resumeCount,
    icon: FileText,
    color: '#2563EB',
    bgColor: 'rgba(37, 99, 235, 0.1)',
    borderColor: 'rgba(37, 99, 235, 0.2)',
    change: null,
    suffix: '',
  },
  {
    label: 'Best ATS Score',
    value: data.atsScore,
    icon: Target,
    color: '#F97316',
    bgColor: 'rgba(249, 115, 22, 0.1)',
    borderColor: 'rgba(249, 115, 22, 0.2)',
    change: null,
    suffix: '%',
  },
  {
    label: 'Jobs Saved',
    value: data.savedJobsCount,
    icon: Send,
    color: '#22C55E',
    bgColor: 'rgba(34, 197, 94, 0.1)',
    borderColor: 'rgba(34, 197, 94, 0.2)',
    change: null,
    suffix: '',
  },
  {
    label: 'Score Improvement',
    value: data.scoreImprovement,
    icon: TrendingUp,
    color: '#F59E0B',
    bgColor: 'rgba(245, 158, 11, 0.1)',
    borderColor: 'rgba(245, 158, 11, 0.2)',
    change: data.scoreImprovement > 0 ? `+${data.scoreImprovement}` : '0',
    suffix: ' pts',
  },
];

export default function StatsGrid(props: StatsGridProps) {
  const data = stats(props);

  return (
    <div className="grid grid-cols-2 lg:grid-cols-4 gap-4">
      {data.map((stat, index) => {
        const Icon = stat.icon;
        return (
          <motion.div
            key={stat.label}
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ duration: 0.5, delay: index * 0.08 }}
            className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-5 hover:bg-white/[0.06] hover:border-white/[0.12] transition-all"
          >
            <div className="flex items-start justify-between mb-4">
              <div
                className="w-9 h-9 rounded-lg flex items-center justify-center"
                style={{
                  background: stat.bgColor,
                  border: `1px solid ${stat.borderColor}`,
                }}
              >
                <Icon className="w-4 h-4" style={{ color: stat.color }} />
              </div>
              {stat.change && (
                <span
                  className="text-xs font-semibold px-2 py-0.5 rounded-full"
                  style={{
                    background: stat.bgColor,
                    color: stat.color,
                    border: `1px solid ${stat.borderColor}`,
                  }}
                >
                  {stat.change}
                </span>
              )}
            </div>
            <div className="space-y-0.5">
              <p className="text-2xl font-bold text-[#F8FAFC]">
                {stat.value}{stat.suffix}
              </p>
              <p className="text-xs text-[#94A3B8]">{stat.label}</p>
            </div>
          </motion.div>
        );
      })}
    </div>
  );
}
