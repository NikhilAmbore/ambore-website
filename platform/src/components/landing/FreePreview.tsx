'use client';

import { useState, useRef } from 'react';
import { useSession } from 'next-auth/react';
import { motion, AnimatePresence } from 'framer-motion';
import { useRouter } from 'next/navigation';
import { Loader2, CheckCircle, Lock, ArrowRight, Sparkles } from 'lucide-react';
import Badge from '@/components/ui/Badge';
import { calculateClientSideScore } from '@/lib/utils';

type Step = 'idle' | 'parsing' | 'matching' | 'scoring' | 'done';

const STEPS: { id: Step; label: string }[] = [
  { id: 'parsing', label: 'Parsing resume' },
  { id: 'matching', label: 'Matching keywords' },
  { id: 'scoring', label: 'Calculating score' },
  { id: 'done', label: 'Done!' },
];

interface ScoreResult {
  score: number;
  atsScore: number;
  keywordMatch: number;
  formatQuality: number;
  missingKeywords: string[];
  matchedKeywords: string[];
}

export default function FreePreview() {
  const { data: session } = useSession();
  const router = useRouter();
  const [jobDesc, setJobDesc] = useState('');
  const [resumeText, setResumeText] = useState('');
  const [step, setStep] = useState<Step>('idle');
  const [result, setResult] = useState<ScoreResult | null>(null);
  const [error, setError] = useState('');
  const resultRef = useRef<HTMLDivElement>(null);

  const currentStepIndex = STEPS.findIndex((s) => s.id === step);

  const handleAnalyze = async () => {
    if (jobDesc.trim().length < 50) {
      setError('Please enter at least 50 characters for the job description.');
      return;
    }
    setError('');
    setResult(null);

    const steps: Step[] = ['parsing', 'matching', 'scoring', 'done'];
    for (const s of steps) {
      setStep(s);
      await new Promise((r) => setTimeout(r, s === 'done' ? 400 : 700 + Math.random() * 400));
    }

    const scoreData = calculateClientSideScore(
      resumeText || 'Generic resume with work experience and skills',
      jobDesc
    );
    setResult(scoreData);

    setTimeout(() => {
      resultRef.current?.scrollIntoView({ behavior: 'smooth', block: 'start' });
    }, 100);
  };

  const handleCTA = () => {
    if (session) {
      router.push('/resume');
    } else {
      router.push('/auth/signup');
    }
  };

  const circumference = 2 * Math.PI * 45;

  return (
    <section id="free-preview" className="py-24 relative overflow-hidden">
      {/* Background */}
      <div className="absolute inset-0 pointer-events-none">
        <div
          className="absolute top-0 left-1/2 -translate-x-1/2 w-[800px] h-[400px] opacity-10"
          style={{
            background: 'radial-gradient(ellipse, rgba(37,99,235,0.5) 0%, transparent 70%)',
            filter: 'blur(80px)',
          }}
        />
      </div>

      <div className="relative max-w-4xl mx-auto px-4 sm:px-6 lg:px-8">
        {/* Header */}
        <div className="text-center mb-12">
          <div className="inline-flex items-center gap-2 px-3 py-1.5 rounded-full bg-[#2563EB]/10 border border-[#2563EB]/20 text-[#60A5FA] text-sm font-medium mb-4">
            <Sparkles className="w-3.5 h-3.5" />
            Try it free — no account needed
          </div>
          <h2 className="text-3xl sm:text-4xl font-bold text-[#F8FAFC] mb-4">
            See your resume score — no signup needed
          </h2>
          <p className="text-[#94A3B8] text-lg max-w-xl mx-auto">
            Paste a job description and your resume to instantly see how well you match.
          </p>
        </div>

        {/* Input Section */}
        <div className="bg-white/[0.03] border border-white/[0.08] rounded-2xl p-6 sm:p-8 mb-8">
          <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
            {/* Job Description */}
            <div className="space-y-2">
              <label className="block text-sm font-medium text-[#CBD5E1]">
                Job Description <span className="text-[#EF4444]">*</span>
              </label>
              <textarea
                value={jobDesc}
                onChange={(e) => setJobDesc(e.target.value)}
                placeholder="Paste the full job description here...&#10;&#10;Required: Software Engineer with 3+ years experience in React, TypeScript, Node.js..."
                rows={8}
                className="w-full bg-white/[0.04] border border-white/10 rounded-lg p-3 text-sm text-[#F8FAFC] placeholder:text-[#475569] resize-none focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
              />
              <p className="text-xs text-[#94A3B8]">
                {jobDesc.length < 50
                  ? `${50 - jobDesc.length} more characters needed`
                  : `${jobDesc.length} characters`}
              </p>
            </div>

            {/* Resume Text */}
            <div className="space-y-2">
              <label className="block text-sm font-medium text-[#CBD5E1]">
                Resume Text <span className="text-[#94A3B8] font-normal">(optional)</span>
              </label>
              <textarea
                value={resumeText}
                onChange={(e) => setResumeText(e.target.value)}
                placeholder="Paste your resume text here...&#10;&#10;Leave empty to see a general score based on the job description alone."
                rows={8}
                className="w-full bg-white/[0.04] border border-white/10 rounded-lg p-3 text-sm text-[#F8FAFC] placeholder:text-[#475569] resize-none focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
              />
              <p className="text-xs text-[#94A3B8]">
                Upload your full resume for a more accurate analysis
              </p>
            </div>
          </div>

          {error && (
            <p className="mt-4 text-sm text-[#EF4444] bg-[#EF4444]/10 border border-[#EF4444]/20 rounded-lg px-4 py-2">
              {error}
            </p>
          )}

          <div className="mt-6 flex justify-center">
            <button
              onClick={handleAnalyze}
              disabled={step !== 'idle' && step !== 'done'}
              className="inline-flex items-center gap-2.5 h-12 px-8 bg-[#F97316] hover:bg-[#EA6D09] disabled:opacity-60 disabled:cursor-not-allowed text-white font-semibold rounded-lg text-base transition-all duration-200 shadow-[0_0_25px_rgba(249,115,22,0.35)] hover:shadow-[0_0_35px_rgba(249,115,22,0.5)]"
            >
              {step !== 'idle' && step !== 'done' ? (
                <>
                  <Loader2 className="w-4 h-4 animate-spin" />
                  Analyzing...
                </>
              ) : (
                <>
                  Analyze My Resume
                  <ArrowRight className="w-4.5 h-4.5" style={{ width: '18px', height: '18px' }} />
                </>
              )}
            </button>
          </div>

          {/* Step Progress */}
          <AnimatePresence>
            {step !== 'idle' && (
              <motion.div
                initial={{ opacity: 0, height: 0 }}
                animate={{ opacity: 1, height: 'auto' }}
                exit={{ opacity: 0, height: 0 }}
                className="mt-6 overflow-hidden"
              >
                <div className="flex items-center justify-center gap-2 flex-wrap">
                  {STEPS.map((s, i) => {
                    const isCompleted = i < currentStepIndex || step === 'done';
                    const isActive = s.id === step && step !== 'done';
                    return (
                      <div key={s.id} className="flex items-center gap-2">
                        <div
                          className={`flex items-center gap-1.5 px-3 py-1 rounded-full text-xs font-medium transition-all ${
                            isCompleted
                              ? 'bg-[#22C55E]/15 text-[#4ADE80] border border-[#22C55E]/20'
                              : isActive
                              ? 'bg-[#F97316]/15 text-[#FB923C] border border-[#F97316]/20'
                              : 'bg-white/5 text-[#94A3B8] border border-white/10'
                          }`}
                        >
                          {isCompleted ? (
                            <CheckCircle className="w-3 h-3" />
                          ) : isActive ? (
                            <Loader2 className="w-3 h-3 animate-spin" />
                          ) : (
                            <div className="w-3 h-3 rounded-full border border-current opacity-40" />
                          )}
                          {s.label}
                        </div>
                        {i < STEPS.length - 1 && (
                          <div className="w-4 h-px bg-white/10" />
                        )}
                      </div>
                    );
                  })}
                </div>
              </motion.div>
            )}
          </AnimatePresence>
        </div>

        {/* Results */}
        <AnimatePresence>
          {result && step === 'done' && (
            <motion.div
              ref={resultRef}
              initial={{ opacity: 0, y: 20 }}
              animate={{ opacity: 1, y: 0 }}
              transition={{ duration: 0.5 }}
            >
              <div className="bg-white/[0.03] border border-white/[0.08] rounded-2xl overflow-hidden">
                {/* Score Header */}
                <div className="p-6 sm:p-8 border-b border-white/[0.06]">
                  <div className="flex flex-col sm:flex-row items-center gap-8">
                    {/* Circular Score */}
                    <div className="relative w-32 h-32 shrink-0">
                      <svg className="w-32 h-32 -rotate-90" viewBox="0 0 110 110">
                        <circle
                          cx="55"
                          cy="55"
                          r="45"
                          fill="none"
                          stroke="rgba(255,255,255,0.06)"
                          strokeWidth="8"
                        />
                        <motion.circle
                          cx="55"
                          cy="55"
                          r="45"
                          fill="none"
                          stroke={result.score >= 70 ? '#22C55E' : result.score >= 50 ? '#F59E0B' : '#EF4444'}
                          strokeWidth="8"
                          strokeLinecap="round"
                          strokeDasharray={circumference}
                          initial={{ strokeDashoffset: circumference }}
                          animate={{
                            strokeDashoffset: circumference * (1 - result.score / 100),
                          }}
                          transition={{ duration: 1.5, ease: 'easeOut' }}
                        />
                      </svg>
                      <div className="absolute inset-0 flex flex-col items-center justify-center">
                        <motion.span
                          className="text-4xl font-bold text-[#F8FAFC]"
                          initial={{ opacity: 0 }}
                          animate={{ opacity: 1 }}
                          transition={{ delay: 0.5 }}
                        >
                          {result.score}
                        </motion.span>
                        <span className="text-xs text-[#94A3B8] mt-0.5">out of 100</span>
                      </div>
                    </div>

                    {/* Metrics */}
                    <div className="flex-1 w-full space-y-4">
                      {[
                        { label: 'ATS Compatibility', value: result.atsScore, color: '#2563EB' },
                        { label: 'Keyword Match', value: result.keywordMatch, color: '#F97316' },
                        { label: 'Format Quality', value: result.formatQuality, color: '#22C55E' },
                      ].map((metric) => (
                        <div key={metric.label}>
                          <div className="flex justify-between text-sm mb-1.5">
                            <span className="text-[#CBD5E1]">{metric.label}</span>
                            <span className="text-[#F8FAFC] font-semibold">{metric.value}%</span>
                          </div>
                          <div className="h-2 bg-white/[0.06] rounded-full overflow-hidden">
                            <motion.div
                              className="h-full rounded-full"
                              style={{ backgroundColor: metric.color }}
                              initial={{ width: 0 }}
                              animate={{ width: `${metric.value}%` }}
                              transition={{ duration: 1, delay: 0.3, ease: 'easeOut' }}
                            />
                          </div>
                        </div>
                      ))}
                    </div>
                  </div>
                </div>

                {/* Insights (partially blurred) */}
                <div className="p-6 sm:p-8">
                  <h3 className="text-base font-semibold text-[#F8FAFC] mb-4">
                    Key Insights
                  </h3>

                  {/* Visible insights */}
                  <div className="space-y-3 mb-4">
                    <div className="flex items-start gap-3 p-3 bg-white/[0.04] rounded-lg border border-white/[0.06]">
                      <div className="w-5 h-5 rounded-full bg-[#F97316]/20 flex items-center justify-center shrink-0 mt-0.5">
                        <span className="text-[#F97316] text-xs font-bold">!</span>
                      </div>
                      <p className="text-sm text-[#CBD5E1]">
                        Your keyword match is {result.keywordMatch}%. Adding more job-specific terms
                        could significantly boost your ATS score.
                      </p>
                    </div>
                    <div className="flex items-start gap-3 p-3 bg-white/[0.04] rounded-lg border border-white/[0.06]">
                      <div className="w-5 h-5 rounded-full bg-[#2563EB]/20 flex items-center justify-center shrink-0 mt-0.5">
                        <span className="text-[#60A5FA] text-xs font-bold">i</span>
                      </div>
                      <p className="text-sm text-[#CBD5E1]">
                        Missing keywords detected:{' '}
                        {result.missingKeywords.slice(0, 3).join(', ')}
                        {result.missingKeywords.length > 3 ? ', and more...' : ''}
                      </p>
                    </div>
                  </div>

                  {/* Blurred locked content */}
                  <div className="relative">
                    <div className="space-y-3 select-none" aria-hidden="true">
                      {[
                        'Your resume is missing quantifiable achievements. Add metrics like "increased sales by 30%".',
                        'The skills section could be restructured to match the job requirements more directly.',
                        'Consider adding a professional summary tailored to this specific role.',
                        'Work experience bullets should start with strong action verbs.',
                        'Education section formatting could be improved for better ATS parsing.',
                      ].map((text, i) => (
                        <div
                          key={i}
                          className="flex items-start gap-3 p-3 bg-white/[0.04] rounded-lg border border-white/[0.06]"
                        >
                          <div className="w-5 h-5 rounded-full bg-white/10 shrink-0 mt-0.5" />
                          <p className="text-sm text-[#CBD5E1]">{text}</p>
                        </div>
                      ))}
                    </div>

                    {/* Blur + CTA overlay */}
                    <div
                      className="absolute inset-0 flex flex-col items-center justify-center gap-4 rounded-xl"
                      style={{
                        background:
                          'linear-gradient(to bottom, transparent 0%, rgba(9,9,11,0.85) 30%, rgba(9,9,11,0.95) 100%)',
                        backdropFilter: 'blur(2px)',
                      }}
                    >
                      <Lock className="w-6 h-6 text-[#94A3B8]" />
                      <div className="text-center px-4">
                        <p className="text-[#F8FAFC] font-semibold text-lg mb-1">
                          Unlock full results
                        </p>
                        <p className="text-[#94A3B8] text-sm mb-4">
                          Create a free account to see all 12 insights, improved bullet points, and save your results.
                        </p>
                        <button
                          onClick={handleCTA}
                          className="inline-flex items-center gap-2 h-11 px-6 bg-[#F97316] hover:bg-[#EA6D09] text-white font-semibold rounded-lg text-sm transition-all shadow-[0_0_20px_rgba(249,115,22,0.35)]"
                        >
                          {session ? 'Get Full Analysis' : 'Create Free Account'}
                          <ArrowRight className="w-4 h-4" />
                        </button>
                        {!session && (
                          <p className="mt-2 text-xs text-[#94A3B8]">
                            Free forever · No credit card
                          </p>
                        )}
                      </div>
                    </div>
                  </div>
                </div>

                {/* Missing keywords preview */}
                {result.missingKeywords.length > 0 && (
                  <div className="px-6 pb-6 sm:px-8 sm:pb-8 border-t border-white/[0.06] pt-5">
                    <h3 className="text-sm font-semibold text-[#F8FAFC] mb-3">
                      Missing Keywords
                    </h3>
                    <div className="flex flex-wrap gap-2">
                      {result.missingKeywords.slice(0, 6).map((kw) => (
                        <Badge key={kw} variant="danger" size="md">
                          {kw}
                        </Badge>
                      ))}
                      <Badge variant="default">
                        +{Math.max(0, result.missingKeywords.length - 6)} more in full report
                      </Badge>
                    </div>
                  </div>
                )}
              </div>
            </motion.div>
          )}
        </AnimatePresence>
      </div>
    </section>
  );
}
