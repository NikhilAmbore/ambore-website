'use client';

export const dynamic = 'force-dynamic';

import { useState, useEffect } from 'react';
import { useSession } from 'next-auth/react';
import { useRouter } from 'next/navigation';
import Sidebar from '@/components/layout/Sidebar';
import { TrendingUp, FileText, Target, MessageSquare, ArrowRight } from 'lucide-react';
import Link from 'next/link';

interface CareerScoreData {
  overall: number;
  resumeScore: number;
  atsScore: number;
  interviewScore: number;
  updatedAt: string;
}

function ScoreRing({ score, size = 120, color }: { score: number; size?: number; color: string }) {
  const radius = (size - 16) / 2;
  const circumference = 2 * Math.PI * radius;
  const offset = circumference - (score / 100) * circumference;

  return (
    <svg width={size} height={size} className="-rotate-90">
      <circle cx={size / 2} cy={size / 2} r={radius} fill="none" stroke="rgba(255,255,255,0.06)" strokeWidth={8} />
      <circle
        cx={size / 2} cy={size / 2} r={radius}
        fill="none"
        stroke={color}
        strokeWidth={8}
        strokeDasharray={circumference}
        strokeDashoffset={offset}
        strokeLinecap="round"
        style={{ transition: 'stroke-dashoffset 1s ease' }}
      />
    </svg>
  );
}

const ACTION_ITEMS = [
  { icon: FileText, label: 'Analyze your resume', href: '/resume', color: 'text-emerald-400', bg: 'bg-emerald-500/10', desc: 'Get AI feedback and ATS score' },
  { icon: Target, label: 'Generate cover letter', href: '/cover-letter', color: 'text-amber-400', bg: 'bg-amber-500/10', desc: 'Tailored to any job description' },
  { icon: MessageSquare, label: 'Practice interviews', href: '/interview', color: 'text-violet-400', bg: 'bg-violet-500/10', desc: 'STAR method answers' },
];

export default function CareerScorePage() {
  const { status } = useSession();
  const router = useRouter();
  const [scores, setScores] = useState<CareerScoreData | null>(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    if (status === 'unauthenticated') router.replace('/auth/signin?callbackUrl=/career-score');
  }, [status, router]);

  useEffect(() => {
    if (status !== 'authenticated') return;
    fetch('/api/user/dashboard')
      .then(r => r.json())
      .then(d => { if (d.success && d.data?.careerScore) setScores(d.data.careerScore); })
      .catch(console.error)
      .finally(() => setLoading(false));
  }, [status]);

  if (status === 'loading' || loading) return (
    <div className="flex h-screen bg-[#09090B] items-center justify-center">
      <div className="w-8 h-8 border-2 border-[#F97316]/30 border-t-[#F97316] rounded-full animate-spin" />
    </div>
  );

  const overall = scores?.overall ?? 0;
  const scoreColor = overall >= 70 ? '#22C55E' : overall >= 40 ? '#F97316' : '#EF4444';

  const scoreItems = [
    { label: 'Resume Quality', value: scores?.resumeScore ?? 0, color: '#22C55E', icon: FileText, href: '/resume' },
    { label: 'ATS Score', value: scores?.atsScore ?? 0, color: '#F97316', icon: Target, href: '/resume' },
    { label: 'Interview Prep', value: scores?.interviewScore ?? 0, color: '#A78BFA', icon: MessageSquare, href: '/interview' },
  ];

  return (
    <div className="flex h-screen bg-[#09090B] overflow-hidden">
      <Sidebar />
      <main className="flex-1 overflow-y-auto">
        <div className="max-w-4xl mx-auto px-4 sm:px-6 lg:px-8 py-8 pt-16 lg:pt-8">
          {/* Header */}
          <div className="mb-8">
            <div className="flex items-center gap-3 mb-2">
              <div className="w-9 h-9 bg-[#F97316]/15 rounded-xl flex items-center justify-center">
                <TrendingUp className="w-5 h-5 text-[#FB923C]" />
              </div>
              <h1 className="text-2xl font-bold text-[#F8FAFC]">Career Score</h1>
            </div>
            <p className="text-[#94A3B8] text-sm">Track your job readiness across resume, ATS optimization, and interview prep.</p>
          </div>

          {/* Overall score */}
          <div className="bg-white/[0.03] border border-white/[0.08] rounded-2xl p-8 mb-6 flex flex-col sm:flex-row items-center gap-8">
            <div className="relative">
              <ScoreRing score={overall} size={160} color={scoreColor} />
              <div className="absolute inset-0 flex flex-col items-center justify-center">
                <span className="text-4xl font-bold text-[#F8FAFC]">{overall}</span>
                <span className="text-xs text-[#64748B]">/ 100</span>
              </div>
            </div>
            <div className="flex-1 text-center sm:text-left">
              <h2 className="text-xl font-bold text-[#F8FAFC] mb-1">
                {overall === 0 ? 'Not started yet' : overall >= 70 ? 'Strong profile' : overall >= 40 ? 'Getting there' : 'Needs work'}
              </h2>
              <p className="text-[#94A3B8] text-sm mb-4">
                {overall === 0
                  ? 'Complete the steps below to build your career score.'
                  : `Your overall job readiness score. ${100 - overall} points away from 100.`}
              </p>
              {scores?.updatedAt && (
                <p className="text-xs text-[#475569]">Last updated {new Date(scores.updatedAt).toLocaleDateString()}</p>
              )}
            </div>
          </div>

          {/* Score breakdown */}
          <div className="grid grid-cols-1 sm:grid-cols-3 gap-4 mb-6">
            {scoreItems.map(item => {
              const Icon = item.icon;
              return (
                <Link key={item.label} href={item.href} className="bg-white/[0.03] border border-white/[0.08] rounded-2xl p-5 hover:border-white/20 transition-all group">
                  <div className="flex items-center justify-between mb-4">
                    <Icon className="w-4 h-4 text-[#64748B]" />
                    <span className="text-2xl font-bold" style={{ color: item.color }}>{item.value}</span>
                  </div>
                  <div className="mb-3">
                    <div className="h-1.5 bg-white/[0.06] rounded-full overflow-hidden">
                      <div
                        className="h-full rounded-full transition-all duration-1000"
                        style={{ width: `${item.value}%`, backgroundColor: item.color }}
                      />
                    </div>
                  </div>
                  <p className="text-sm font-medium text-[#94A3B8] group-hover:text-[#F8FAFC] transition-colors">{item.label}</p>
                </Link>
              );
            })}
          </div>

          {/* Action items */}
          <div className="bg-white/[0.02] border border-white/[0.06] rounded-2xl p-6">
            <h3 className="text-sm font-semibold text-[#F8FAFC] mb-4">Improve your score</h3>
            <div className="space-y-3">
              {ACTION_ITEMS.map(item => {
                const Icon = item.icon;
                return (
                  <Link
                    key={item.href}
                    href={item.href}
                    className="flex items-center gap-4 p-4 rounded-xl hover:bg-white/[0.04] transition-all group"
                  >
                    <div className={`w-9 h-9 ${item.bg} rounded-lg flex items-center justify-center shrink-0`}>
                      <Icon className={`w-4 h-4 ${item.color}`} />
                    </div>
                    <div className="flex-1 min-w-0">
                      <p className="text-sm font-medium text-[#F8FAFC]">{item.label}</p>
                      <p className="text-xs text-[#64748B]">{item.desc}</p>
                    </div>
                    <ArrowRight className="w-4 h-4 text-[#475569] group-hover:text-[#94A3B8] transition-colors" />
                  </Link>
                );
              })}
            </div>
          </div>
        </div>
      </main>
    </div>
  );
}
