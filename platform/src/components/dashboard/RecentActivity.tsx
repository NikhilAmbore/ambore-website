'use client';

import { motion } from 'framer-motion';
import { FileText, Bookmark, Send, MessageSquare, TrendingUp, UserPlus, PenLine, Linkedin } from 'lucide-react';
import type { ActivityLog } from '@/types';
import { formatDate } from '@/lib/utils';

interface RecentActivityProps {
  activities: ActivityLog[];
}

type KnownType =
  | 'resume_analyzed'
  | 'job_saved'
  | 'job_applied'
  | 'interview_practiced'
  | 'score_updated'
  | 'account_created'
  | 'cover_letter_generated'
  | 'linkedin_optimized';

const activityConfig: Record<KnownType, {
  icon: React.ComponentType<{ className?: string; style?: React.CSSProperties }>;
  color: string;
  bgColor: string;
  label: (metadata?: Record<string, unknown> | null) => string;
}> = {
  resume_analyzed: {
    icon: FileText,
    color: '#2563EB',
    bgColor: 'rgba(37, 99, 235, 0.15)',
    label: (meta) => `Analyzed resume${meta?.jobDescription ? ` for a role` : ''}`,
  },
  job_saved: {
    icon: Bookmark,
    color: '#F97316',
    bgColor: 'rgba(249, 115, 22, 0.15)',
    label: (meta) => `Saved job: ${meta?.jobTitle ?? 'Unknown Position'}`,
  },
  job_applied: {
    icon: Send,
    color: '#22C55E',
    bgColor: 'rgba(34, 197, 94, 0.15)',
    label: (meta) => `Applied to ${meta?.company ?? 'a company'}`,
  },
  interview_practiced: {
    icon: MessageSquare,
    color: '#A78BFA',
    bgColor: 'rgba(167, 139, 250, 0.15)',
    label: (meta) => `Practiced interview${meta?.role ? ` for ${meta.role}` : ''}`,
  },
  score_updated: {
    icon: TrendingUp,
    color: '#22C55E',
    bgColor: 'rgba(34, 197, 94, 0.15)',
    label: (meta) => `Career score updated to ${meta?.score ?? '—'}`,
  },
  account_created: {
    icon: UserPlus,
    color: '#F97316',
    bgColor: 'rgba(249, 115, 22, 0.15)',
    label: () => 'Account created — welcome!',
  },
  cover_letter_generated: {
    icon: PenLine,
    color: '#F59E0B',
    bgColor: 'rgba(245, 158, 11, 0.15)',
    label: (meta) => `Generated cover letter${meta?.tone ? ` (${meta.tone})` : ''}`,
  },
  linkedin_optimized: {
    icon: Linkedin,
    color: '#60A5FA',
    bgColor: 'rgba(96, 165, 250, 0.15)',
    label: (meta) => `Optimized LinkedIn ${meta?.section ?? 'section'}`,
  },
};

export default function RecentActivity({ activities }: RecentActivityProps) {
  return (
    <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-5">
      <h2 className="text-sm font-semibold text-[#F8FAFC] mb-4">Recent Activity</h2>

      {activities.length === 0 ? (
        <div className="text-center py-8">
          <p className="text-[#94A3B8] text-sm">No activity yet.</p>
          <p className="text-[#475569] text-xs mt-1">Start by analyzing a resume!</p>
        </div>
      ) : (
        <div className="relative">
          <div className="absolute left-4 top-4 bottom-4 w-px bg-white/[0.06]" />
          <div className="space-y-4">
            {activities.map((activity, index) => {
              const config = activityConfig[activity.type as KnownType];
              if (!config) return null;
              const Icon = config.icon;

              return (
                <motion.div
                  key={activity.id}
                  initial={{ opacity: 0, x: -10 }}
                  animate={{ opacity: 1, x: 0 }}
                  transition={{ duration: 0.3, delay: index * 0.05 }}
                  className="flex items-start gap-4 pl-8 relative"
                >
                  <div className="absolute" style={{ left: '-4px', top: '4px' }}>
                    <div
                      className="w-8 h-8 rounded-full flex items-center justify-center shrink-0"
                      style={{ background: config.bgColor }}
                    >
                      <Icon className="w-3.5 h-3.5" style={{ color: config.color }} />
                    </div>
                  </div>
                  <div className="flex-1 min-w-0">
                    <p className="text-sm text-[#CBD5E1] leading-snug">
                      {config.label(activity.metadata as Record<string, unknown> | null)}
                    </p>
                    <p className="text-xs text-[#94A3B8] mt-0.5">
                      {formatDate(activity.createdAt)}
                    </p>
                  </div>
                </motion.div>
              );
            })}
          </div>
        </div>
      )}
    </div>
  );
}
