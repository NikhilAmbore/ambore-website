'use client';

export const dynamic = 'force-dynamic';

import { useEffect, useState } from 'react';
import { useSession } from 'next-auth/react';
import { useRouter } from 'next/navigation';
import Link from 'next/link';
import Sidebar from '@/components/layout/Sidebar';
import CareerScore from '@/components/dashboard/CareerScore';
import StatsGrid from '@/components/dashboard/StatsGrid';
import RecentActivity from '@/components/dashboard/RecentActivity';
import { FileText, Briefcase, ArrowRight, Sparkles, PenLine, MessageSquare } from 'lucide-react';
import type { CareerScore as CareerScoreType, ActivityLog } from '@/types';

interface DashboardData {
  careerScore: CareerScoreType | null;
  recentActivities: ActivityLog[];
  resumeCount: number;
  savedJobsCount: number;
}

export default function DashboardPage() {
  const { data: session, status } = useSession();
  const router = useRouter();
  const [dashData, setDashData] = useState<DashboardData>({
    careerScore: null,
    recentActivities: [],
    resumeCount: 0,
    savedJobsCount: 0,
  });
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    if (status === 'unauthenticated') router.replace('/auth/signin?callbackUrl=/dashboard');
  }, [status, router]);

  useEffect(() => {
    if (status !== 'authenticated') return;
    fetch('/api/user/dashboard')
      .then(r => r.json())
      .then(d => {
        if (d.success && d.data) {
          setDashData({
            careerScore: d.data.careerScore,
            recentActivities: d.data.recentActivities ?? [],
            resumeCount: d.data.resumeCount ?? 0,
            savedJobsCount: d.data.savedJobsCount ?? 0,
          });
        }
      })
      .catch(console.error)
      .finally(() => setLoading(false));
  }, [status]);

  if (status === 'loading' || (status === 'authenticated' && loading)) {
    return (
      <div className="flex h-screen items-center justify-center bg-[#09090B]">
        <div className="w-6 h-6 border-2 border-[#F97316] border-t-transparent rounded-full animate-spin" />
      </div>
    );
  }

  if (!session?.user) return null;

  const firstName = session.user.name?.split(' ')[0] ?? 'there';

  return (
    <div className="flex h-screen bg-[#09090B] overflow-hidden">
      <Sidebar />
      <main className="flex-1 overflow-y-auto">
        <div className="max-w-6xl mx-auto px-4 sm:px-6 lg:px-8 py-8 pt-16 lg:pt-8">
          {/* Header */}
          <div className="mb-8">
            <h1 className="text-2xl font-bold text-[#F8FAFC] mb-1">
              Welcome back, {firstName}!
            </h1>
            <p className="text-[#94A3B8] text-sm">Here&rsquo;s your career progress at a glance.</p>
          </div>

          {/* Quick Actions */}
          <div className="grid grid-cols-2 lg:grid-cols-4 gap-3 mb-8">
            {[
              { href: '/resume', icon: Sparkles, label: 'Analyze Resume', sub: 'Get ATS score', color: '#F97316', bg: 'from-[#F97316]/15' },
              { href: '/cover-letter', icon: PenLine, label: 'Cover Letter', sub: 'AI-tailored', color: '#F59E0B', bg: 'from-[#F59E0B]/15' },
              { href: '/interview', icon: MessageSquare, label: 'Interview Prep', sub: 'STAR answers', color: '#A78BFA', bg: 'from-[#A78BFA]/15' },
              { href: '/jobs', icon: Briefcase, label: 'Browse Jobs', sub: '60K+ listings', color: '#60A5FA', bg: 'from-[#60A5FA]/15' },
            ].map(item => {
              const Icon = item.icon;
              return (
                <Link
                  key={item.href}
                  href={item.href}
                  className={`flex items-center justify-between p-4 bg-gradient-to-r ${item.bg} to-transparent border rounded-xl hover:border-white/20 transition-all group`}
                  style={{ borderColor: `${item.color}20` }}
                >
                  <div>
                    <p className="text-sm font-semibold text-[#F8FAFC]">{item.label}</p>
                    <p className="text-xs text-[#94A3B8]">{item.sub}</p>
                  </div>
                  <div className="w-8 h-8 rounded-lg flex items-center justify-center shrink-0" style={{ background: `${item.color}20` }}>
                    <Icon className="w-4 h-4" style={{ color: item.color }} />
                  </div>
                </Link>
              );
            })}
          </div>

          {/* Stats */}
          <div className="mb-6">
            <StatsGrid
              resumeCount={dashData.resumeCount}
              savedJobsCount={dashData.savedJobsCount}
              atsScore={dashData.careerScore?.atsScore ?? 0}
              scoreImprovement={dashData.careerScore?.overall ?? 0}
            />
          </div>

          {/* Career Score + Activity */}
          <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
            <CareerScore score={dashData.careerScore} />
            <RecentActivity activities={dashData.recentActivities} />
          </div>

          {/* Empty state for new users */}
          {dashData.resumeCount === 0 && !loading && (
            <div className="mt-6 p-8 bg-white/[0.03] border border-dashed border-white/15 rounded-xl text-center">
              <FileText className="w-10 h-10 text-[#94A3B8] mx-auto mb-3" />
              <h3 className="text-base font-semibold text-[#F8FAFC] mb-1">Start with your first analysis</h3>
              <p className="text-sm text-[#94A3B8] mb-4 max-w-sm mx-auto">
                Upload your resume and paste a job description to get your ATS score and AI-powered suggestions.
              </p>
              <Link
                href="/resume"
                className="inline-flex items-center gap-2 h-9 px-5 bg-[#F97316] hover:bg-[#EA6D09] text-white text-sm font-medium rounded-lg transition-all"
              >
                Analyze My Resume <ArrowRight className="w-3.5 h-3.5" />
              </Link>
            </div>
          )}
        </div>
      </main>
    </div>
  );
}
