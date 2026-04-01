'use client';

export const dynamic = 'force-dynamic';

import { useState, useEffect } from 'react';
import { useSession } from 'next-auth/react';
import { useRouter } from 'next/navigation';
import Sidebar from '@/components/layout/Sidebar';
import { Sparkles, Copy, Check, RotateCcw } from 'lucide-react';
import toast from 'react-hot-toast';

const TONES = [
  { value: 'professional', label: 'Professional', desc: 'Formal & achievement-focused' },
  { value: 'enthusiastic', label: 'Enthusiastic', desc: 'Passionate & energetic' },
  { value: 'concise', label: 'Concise', desc: 'Short & punchy (under 250 words)' },
] as const;

type Tone = typeof TONES[number]['value'];

export default function CoverLetterPage() {
  const { status } = useSession();
  const router = useRouter();
  const [resumeText, setResumeText] = useState('');
  const [jobDescription, setJobDescription] = useState('');
  const [tone, setTone] = useState<Tone>('professional');
  const [coverLetter, setCoverLetter] = useState('');
  const [loading, setLoading] = useState(false);
  const [copied, setCopied] = useState(false);

  useEffect(() => {
    if (status === 'unauthenticated') router.replace('/auth/signin?callbackUrl=/cover-letter');
  }, [status, router]);

  if (status === 'loading') return (
    <div className="flex h-screen bg-[#09090B] items-center justify-center">
      <div className="w-6 h-6 border-2 border-[#F97316]/30 border-t-[#F97316] rounded-full animate-spin" />
    </div>
  );

  const generate = async () => {
    if (!resumeText.trim()) { toast.error('Please paste your resume'); return; }
    if (!jobDescription.trim()) { toast.error('Please paste the job description'); return; }
    setLoading(true);
    try {
      const res = await fetch('/api/cover-letter', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ resumeText, jobDescription, tone }),
      });
      const data = await res.json();
      if (!res.ok) throw new Error(data.error ?? 'Failed');
      setCoverLetter(data.coverLetter);
      toast.success('Cover letter generated!');
    } catch (err: unknown) {
      toast.error(err instanceof Error ? err.message : 'Failed to generate');
    } finally {
      setLoading(false);
    }
  };

  const copy = () => {
    navigator.clipboard.writeText(coverLetter);
    setCopied(true);
    toast.success('Copied to clipboard!');
    setTimeout(() => setCopied(false), 2000);
  };

  return (
    <div className="flex h-screen bg-[#09090B] overflow-hidden">
      <Sidebar />
      <main className="flex-1 overflow-y-auto">
        <div className="max-w-5xl mx-auto px-4 sm:px-6 py-6 pt-16 lg:pt-8">

          {/* Header */}
          <div className="mb-6">
            <h1 className="text-xl sm:text-2xl font-bold text-[#F8FAFC]">Cover Letter Generator</h1>
            <p className="text-[#94A3B8] text-sm mt-1">Paste your resume and job description — get a tailored cover letter in seconds.</p>
          </div>

          {/* Tone selector */}
          <div className="mb-5">
            <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">Tone</label>
            <div className="flex gap-2 flex-wrap">
              {TONES.map(t => (
                <button
                  key={t.value}
                  onClick={() => setTone(t.value)}
                  className={`px-4 py-2.5 rounded-xl border text-left transition-all text-sm ${
                    tone === t.value
                      ? 'bg-[#F97316]/10 border-[#F97316]/40 text-[#FB923C]'
                      : 'bg-white/[0.02] border-white/[0.07] text-[#94A3B8] hover:border-white/20'
                  }`}
                >
                  <span className="font-semibold">{t.label}</span>
                  <span className="text-xs opacity-60 ml-2 hidden sm:inline">{t.desc}</span>
                </button>
              ))}
            </div>
          </div>

          {/* Inputs */}
          <div className="grid grid-cols-1 lg:grid-cols-2 gap-4 mb-5">
            <div>
              <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">Your Resume</label>
              <textarea
                value={resumeText}
                onChange={e => setResumeText(e.target.value)}
                rows={10}
                placeholder="Paste your resume text here..."
                className="w-full bg-white/[0.03] border border-white/[0.08] rounded-xl p-4 text-[#F8FAFC] text-sm placeholder-[#475569] resize-none outline-none focus:border-[#F97316]/50 transition-colors"
              />
            </div>
            <div>
              <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">Job Description</label>
              <textarea
                value={jobDescription}
                onChange={e => setJobDescription(e.target.value)}
                rows={10}
                placeholder="Paste the full job description here..."
                className="w-full bg-white/[0.03] border border-white/[0.08] rounded-xl p-4 text-[#F8FAFC] text-sm placeholder-[#475569] resize-none outline-none focus:border-[#F97316]/50 transition-colors"
              />
            </div>
          </div>

          <button
            onClick={generate}
            disabled={loading}
            className="w-full h-11 bg-[#F97316] hover:bg-[#EA6D09] disabled:opacity-50 text-white font-semibold rounded-xl flex items-center justify-center gap-2 transition-all text-sm"
          >
            {loading
              ? <><div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" /> Generating...</>
              : <><Sparkles className="w-4 h-4" /> Generate Cover Letter</>}
          </button>

          {/* Result */}
          {coverLetter && (
            <div className="mt-6 bg-white/[0.03] border border-white/[0.08] rounded-xl p-5">
              <div className="flex items-center justify-between mb-4">
                <h2 className="font-semibold text-[#F8FAFC] text-sm">Your Cover Letter</h2>
                <div className="flex gap-2">
                  <button
                    onClick={generate}
                    disabled={loading}
                    className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium text-[#94A3B8] hover:text-[#F8FAFC] bg-white/[0.04] hover:bg-white/[0.08] rounded-lg transition-all"
                  >
                    <RotateCcw className="w-3 h-3" /> Regenerate
                  </button>
                  <button
                    onClick={copy}
                    className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium bg-[#F97316]/10 text-[#FB923C] hover:bg-[#F97316]/20 rounded-lg transition-all"
                  >
                    {copied ? <Check className="w-3 h-3" /> : <Copy className="w-3 h-3" />}
                    {copied ? 'Copied!' : 'Copy'}
                  </button>
                </div>
              </div>
              <pre className="text-[#CBD5E1] text-sm leading-relaxed whitespace-pre-wrap font-sans">{coverLetter}</pre>
            </div>
          )}
        </div>
      </main>
    </div>
  );
}
