'use client';

export const dynamic = 'force-dynamic';

import { useState, useEffect } from 'react';
import { useSession } from 'next-auth/react';
import { useRouter } from 'next/navigation';
import Sidebar from '@/components/layout/Sidebar';
import { Sparkles, Copy, Check } from 'lucide-react';
import toast from 'react-hot-toast';

type Section = 'headline' | 'summary' | 'experience';

const SECTIONS: { value: Section; label: string; desc: string; placeholder: string }[] = [
  {
    value: 'headline',
    label: 'Headline',
    desc: '220-char tagline',
    placeholder: 'e.g. Software Engineer at Acme Corp',
  },
  {
    value: 'summary',
    label: 'About / Summary',
    desc: 'Your "About" section',
    placeholder: 'Paste your current LinkedIn summary here...',
  },
  {
    value: 'experience',
    label: 'Experience',
    desc: 'Job bullet points',
    placeholder: '- Led team of 5 engineers\n- Worked on backend systems\n- Helped improve performance',
  },
];

export default function LinkedInPage() {
  const { status } = useSession();
  const router = useRouter();
  const [section, setSection] = useState<Section>('headline');
  const [currentText, setCurrentText] = useState('');
  const [targetRole, setTargetRole] = useState('');
  const [industry, setIndustry] = useState('');
  const [optimized, setOptimized] = useState('');
  const [loading, setLoading] = useState(false);
  const [copied, setCopied] = useState(false);

  useEffect(() => {
    if (status === 'unauthenticated') router.replace('/auth/signin?callbackUrl=/linkedin');
  }, [status, router]);

  if (status === 'loading') return (
    <div className="flex h-screen bg-[#09090B] items-center justify-center">
      <div className="w-6 h-6 border-2 border-[#F97316]/30 border-t-[#F97316] rounded-full animate-spin" />
    </div>
  );

  const optimize = async () => {
    if (!currentText.trim()) { toast.error('Please paste your current content first'); return; }
    setLoading(true);
    try {
      const res = await fetch('/api/linkedin', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          section,
          currentText,
          targetRole: targetRole || undefined,
          industry: industry || undefined,
        }),
      });
      const data = await res.json();
      if (!res.ok) throw new Error(data.error ?? 'Failed');
      setOptimized(data.optimized);
      toast.success('Optimized!');
    } catch (err: unknown) {
      toast.error(err instanceof Error ? err.message : 'Failed to optimize');
    } finally {
      setLoading(false);
    }
  };

  const copy = () => {
    navigator.clipboard.writeText(optimized);
    setCopied(true);
    toast.success('Copied!');
    setTimeout(() => setCopied(false), 2000);
  };

  const activeSection = SECTIONS.find(s => s.value === section)!;

  return (
    <div className="flex h-screen bg-[#09090B] overflow-hidden">
      <Sidebar />
      <main className="flex-1 overflow-y-auto">
        <div className="max-w-4xl mx-auto px-4 sm:px-6 py-6 pt-16 lg:pt-8">

          {/* Header */}
          <div className="mb-6">
            <h1 className="text-xl sm:text-2xl font-bold text-[#F8FAFC]">LinkedIn Optimizer</h1>
            <p className="text-[#94A3B8] text-sm mt-1">Rewrite your headline, summary, and experience bullets to attract more recruiters.</p>
          </div>

          {/* Section tabs */}
          <div className="flex gap-2 mb-5 flex-wrap">
            {SECTIONS.map(s => (
              <button
                key={s.value}
                onClick={() => { setSection(s.value); setOptimized(''); setCopied(false); }}
                className={`px-4 py-2.5 rounded-xl border text-sm text-left transition-all ${
                  section === s.value
                    ? 'bg-blue-500/10 border-blue-500/40 text-blue-400'
                    : 'bg-white/[0.02] border-white/[0.07] text-[#94A3B8] hover:border-white/20'
                }`}
              >
                <span className="font-semibold">{s.label}</span>
                <span className="text-xs opacity-60 ml-2 hidden sm:inline">{s.desc}</span>
              </button>
            ))}
          </div>

          <div className="grid grid-cols-1 lg:grid-cols-2 gap-5">
            {/* Input */}
            <div className="space-y-4">
              <div>
                <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">
                  Current {activeSection.label}
                </label>
                <textarea
                  value={currentText}
                  onChange={e => setCurrentText(e.target.value)}
                  rows={section === 'headline' ? 3 : 8}
                  placeholder={activeSection.placeholder}
                  className="w-full bg-white/[0.03] border border-white/[0.08] rounded-xl p-4 text-[#F8FAFC] text-sm placeholder-[#475569] resize-none outline-none focus:border-blue-500/40 transition-colors"
                />
              </div>
              <div className="grid grid-cols-2 gap-3">
                <div>
                  <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">Target Role</label>
                  <input
                    value={targetRole}
                    onChange={e => setTargetRole(e.target.value)}
                    placeholder="e.g. Senior PM"
                    className="w-full bg-white/[0.03] border border-white/[0.08] rounded-xl px-4 py-2.5 text-[#F8FAFC] text-sm placeholder-[#475569] outline-none focus:border-blue-500/40 transition-colors"
                  />
                </div>
                <div>
                  <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">Industry</label>
                  <input
                    value={industry}
                    onChange={e => setIndustry(e.target.value)}
                    placeholder="e.g. Fintech"
                    className="w-full bg-white/[0.03] border border-white/[0.08] rounded-xl px-4 py-2.5 text-[#F8FAFC] text-sm placeholder-[#475569] outline-none focus:border-blue-500/40 transition-colors"
                  />
                </div>
              </div>
              <button
                onClick={optimize}
                disabled={loading}
                className="w-full h-11 bg-blue-600 hover:bg-blue-700 disabled:opacity-50 text-white font-semibold rounded-xl flex items-center justify-center gap-2 transition-all text-sm"
              >
                {loading
                  ? <><div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" /> Optimizing...</>
                  : <><Sparkles className="w-4 h-4" /> Optimize {activeSection.label}</>}
              </button>
            </div>

            {/* Output */}
            <div>
              <div className="flex items-center justify-between mb-2">
                <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider">Optimized Version</label>
                {optimized && (
                  <button
                    onClick={copy}
                    className="flex items-center gap-1.5 text-xs font-medium text-[#94A3B8] hover:text-[#F8FAFC] bg-white/[0.04] hover:bg-white/[0.08] px-3 py-1.5 rounded-lg transition-all"
                  >
                    {copied ? <Check className="w-3 h-3 text-green-400" /> : <Copy className="w-3 h-3" />}
                    {copied ? 'Copied!' : 'Copy'}
                  </button>
                )}
              </div>
              {optimized ? (
                <div className="bg-white/[0.03] border border-blue-500/20 rounded-xl p-4">
                  <pre className="text-[#CBD5E1] text-sm leading-relaxed whitespace-pre-wrap font-sans">{optimized}</pre>
                </div>
              ) : (
                <div className="min-h-[200px] bg-white/[0.02] border border-dashed border-white/[0.08] rounded-xl flex items-center justify-center">
                  <p className="text-[#475569] text-sm text-center px-6">
                    Your optimized {activeSection.label.toLowerCase()} will appear here
                  </p>
                </div>
              )}
            </div>
          </div>
        </div>
      </main>
    </div>
  );
}
