'use client';

export const dynamic = 'force-dynamic';

import { useState, useEffect, Suspense } from 'react';
import { useSession } from 'next-auth/react';
import { useRouter, useSearchParams } from 'next/navigation';
import Sidebar from '@/components/layout/Sidebar';
import ResumeUpload from '@/components/resume/ResumeUpload';
import AnalysisResults from '@/components/resume/AnalysisResults';
import type { AnalysisResult } from '@/types';

function ResumeContent() {
  const { data: session, status } = useSession();
  const router = useRouter();
  const searchParams = useSearchParams();
  const [result, setResult] = useState<AnalysisResult | null>(null);

  const initialJobDescription = searchParams.get('jobDescription') ?? '';

  useEffect(() => {
    if (status === 'unauthenticated') {
      router.replace('/auth/signin?callbackUrl=/resume');
    }
  }, [status, router]);

  if (status === 'loading' || status === 'unauthenticated') {
    return (
      <div className="flex h-screen bg-[#09090B] items-center justify-center">
        <div className="w-8 h-8 border-2 border-[#F97316]/30 border-t-[#F97316] rounded-full animate-spin" />
      </div>
    );
  }

  if (!session?.user) {
    return null;
  }

  return (
    <div className="flex h-screen bg-[#09090B] overflow-hidden">
      <Sidebar />

      <main className="flex-1 overflow-y-auto">
        <div className="max-w-5xl mx-auto px-4 sm:px-6 lg:px-8 py-8 pt-16 lg:pt-8">
          {/* Header */}
          <div className="mb-8">
            <h1 className="text-2xl font-bold text-[#F8FAFC] mb-1">Resume Analyzer</h1>
            <p className="text-[#94A3B8] text-sm">
              Upload your resume and a job description to get your ATS score and AI-powered
              improvement suggestions.
            </p>
          </div>

          {/* Upload */}
          <div className="mb-6">
            <ResumeUpload
              onAnalysisComplete={(r) => setResult(r)}
              initialJobDescription={initialJobDescription}
            />
          </div>

          {/* Results */}
          {result && <AnalysisResults result={result} />}
        </div>
      </main>
    </div>
  );
}

export default function ResumePage() {
  return (
    <Suspense fallback={
      <div className="flex h-screen bg-[#09090B] items-center justify-center">
        <div className="w-8 h-8 border-2 border-[#F97316]/30 border-t-[#F97316] rounded-full animate-spin" />
      </div>
    }>
      <ResumeContent />
    </Suspense>
  );
}
