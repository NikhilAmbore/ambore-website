'use client';

export const dynamic = 'force-dynamic';

import { useState, useEffect } from 'react';
import { useSession } from 'next-auth/react';
import { useRouter } from 'next/navigation';
import Sidebar from '@/components/layout/Sidebar';
import { Sparkles, ChevronDown, ChevronUp, Copy, RotateCcw } from 'lucide-react';
import toast from 'react-hot-toast';

const COMMON_QUESTIONS = [
  'Tell me about a time you had to meet a tight deadline.',
  'Describe a situation where you had a conflict with a teammate.',
  'Tell me about a project you are most proud of.',
  'How did you handle a time when you failed or made a mistake?',
  'Describe a time you had to learn something new quickly.',
  'Tell me about a time you led a team.',
  'How did you handle competing priorities under pressure?',
  'Describe a time you disagreed with your manager.',
];

export default function InterviewPage() {
  const { status } = useSession();
  const router = useRouter();
  const [question, setQuestion] = useState('');
  const [role, setRole] = useState('');
  const [company, setCompany] = useState('');
  const [context, setContext] = useState('');
  const [answer, setAnswer] = useState('');
  const [loading, setLoading] = useState(false);
  const [showContext, setShowContext] = useState(false);
  const [history, setHistory] = useState<{ question: string; answer: string }[]>([]);
  const [showQuestions, setShowQuestions] = useState(false);

  useEffect(() => {
    if (status === 'unauthenticated') router.replace('/auth/signin?callbackUrl=/interview');
  }, [status, router]);

  if (status === 'loading') return (
    <div className="flex h-screen bg-[#09090B] items-center justify-center">
      <div className="w-6 h-6 border-2 border-[#F97316]/30 border-t-[#F97316] rounded-full animate-spin" />
    </div>
  );

  const generate = async () => {
    if (!question.trim()) { toast.error('Please enter an interview question'); return; }
    setLoading(true);
    try {
      const res = await fetch('/api/interview', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          question,
          role: role || undefined,
          company: company || undefined,
          context: context || undefined,
        }),
      });
      const data = await res.json();
      if (!res.ok) throw new Error(data.error ?? 'Failed');
      setAnswer(data.answer);
      setHistory(prev => [{ question, answer: data.answer }, ...prev.slice(0, 4)]);
      toast.success('Answer generated!');
    } catch (err: unknown) {
      toast.error(err instanceof Error ? err.message : 'Failed to generate answer');
    } finally {
      setLoading(false);
    }
  };

  const formatAnswer = (text: string) => {
    return text.split('\n').map((line, i) => {
      const boldMatch = line.match(/^\*\*(.+?):\*\*\s*(.*)/);
      if (boldMatch) {
        return (
          <div key={i} className="mb-3">
            <span className="text-[#FB923C] font-semibold">{boldMatch[1]}: </span>
            <span className="text-[#CBD5E1]">{boldMatch[2]}</span>
          </div>
        );
      }
      if (!line.trim()) return null;
      return <p key={i} className="text-[#CBD5E1] text-sm mb-2">{line}</p>;
    }).filter(Boolean);
  };

  return (
    <div className="flex h-screen bg-[#09090B] overflow-hidden">
      <Sidebar />
      <main className="flex-1 overflow-y-auto">
        <div className="max-w-4xl mx-auto px-4 sm:px-6 py-6 pt-16 lg:pt-8">

          {/* Header */}
          <div className="mb-6">
            <h1 className="text-xl sm:text-2xl font-bold text-[#F8FAFC]">Interview Practice</h1>
            <p className="text-[#94A3B8] text-sm mt-1">Get STAR-method answers tailored to your target role.</p>
          </div>

          <div className="grid grid-cols-1 lg:grid-cols-3 gap-5">
            {/* Main form */}
            <div className="lg:col-span-2 space-y-4">

              {/* Common questions — mobile accordion */}
              <div className="lg:hidden bg-white/[0.03] border border-white/[0.07] rounded-xl overflow-hidden">
                <button
                  onClick={() => setShowQuestions(!showQuestions)}
                  className="w-full flex items-center justify-between px-4 py-3 text-sm font-medium text-[#F8FAFC]"
                >
                  Common Questions
                  {showQuestions ? <ChevronUp className="w-4 h-4 text-[#94A3B8]" /> : <ChevronDown className="w-4 h-4 text-[#94A3B8]" />}
                </button>
                {showQuestions && (
                  <div className="border-t border-white/[0.06] p-2 grid grid-cols-1 sm:grid-cols-2 gap-1">
                    {COMMON_QUESTIONS.map((q, i) => (
                      <button
                        key={i}
                        onClick={() => { setQuestion(q); setShowQuestions(false); }}
                        className="text-left text-xs text-[#64748B] hover:text-[#94A3B8] py-2 px-3 rounded-lg hover:bg-white/[0.04] transition-all leading-relaxed"
                      >
                        {q}
                      </button>
                    ))}
                  </div>
                )}
              </div>

              {/* Question textarea */}
              <div>
                <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">Interview Question</label>
                <textarea
                  value={question}
                  onChange={e => setQuestion(e.target.value)}
                  rows={3}
                  placeholder="e.g. Tell me about a time you had to handle a difficult stakeholder..."
                  className="w-full bg-white/[0.03] border border-white/[0.08] rounded-xl p-4 text-[#F8FAFC] text-sm placeholder-[#475569] resize-none outline-none focus:border-[#F97316]/50 transition-colors"
                />
              </div>

              {/* Role & Company */}
              <div className="grid grid-cols-2 gap-3">
                <div>
                  <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">Target Role</label>
                  <input
                    value={role}
                    onChange={e => setRole(e.target.value)}
                    placeholder="e.g. Product Manager"
                    className="w-full bg-white/[0.03] border border-white/[0.08] rounded-xl px-4 py-2.5 text-[#F8FAFC] text-sm placeholder-[#475569] outline-none focus:border-[#F97316]/50 transition-colors"
                  />
                </div>
                <div>
                  <label className="block text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-2">Company</label>
                  <input
                    value={company}
                    onChange={e => setCompany(e.target.value)}
                    placeholder="e.g. Google"
                    className="w-full bg-white/[0.03] border border-white/[0.08] rounded-xl px-4 py-2.5 text-[#F8FAFC] text-sm placeholder-[#475569] outline-none focus:border-[#F97316]/50 transition-colors"
                  />
                </div>
              </div>

              {/* Context toggle */}
              <div>
                <button
                  onClick={() => setShowContext(!showContext)}
                  className="flex items-center gap-1.5 text-xs font-medium text-[#64748B] hover:text-[#94A3B8] transition-colors"
                >
                  {showContext ? <ChevronUp className="w-3.5 h-3.5" /> : <ChevronDown className="w-3.5 h-3.5" />}
                  Add background context (optional)
                </button>
                {showContext && (
                  <textarea
                    value={context}
                    onChange={e => setContext(e.target.value)}
                    rows={3}
                    placeholder="Paste relevant experience, projects, or skills to personalize the answer..."
                    className="mt-2 w-full bg-white/[0.03] border border-white/[0.08] rounded-xl p-4 text-[#F8FAFC] text-sm placeholder-[#475569] resize-none outline-none focus:border-[#F97316]/50 transition-colors"
                  />
                )}
              </div>

              <button
                onClick={generate}
                disabled={loading}
                className="w-full h-11 bg-[#F97316] hover:bg-[#EA6D09] disabled:opacity-50 text-white font-semibold rounded-xl flex items-center justify-center gap-2 transition-all text-sm"
              >
                {loading
                  ? <><div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" /> Generating...</>
                  : <><Sparkles className="w-4 h-4" /> Generate STAR Answer</>}
              </button>

              {/* Answer */}
              {answer && (
                <div className="bg-white/[0.03] border border-white/[0.08] rounded-xl p-5">
                  <div className="flex items-center justify-between mb-4">
                    <h2 className="font-semibold text-[#F8FAFC] text-sm">STAR Answer</h2>
                    <div className="flex gap-2">
                      <button
                        onClick={generate}
                        className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium text-[#94A3B8] hover:text-[#F8FAFC] bg-white/[0.04] hover:bg-white/[0.08] rounded-lg transition-all"
                      >
                        <RotateCcw className="w-3 h-3" /> Retry
                      </button>
                      <button
                        onClick={() => { navigator.clipboard.writeText(answer); toast.success('Copied!'); }}
                        className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium text-[#94A3B8] hover:text-[#F8FAFC] bg-white/[0.04] hover:bg-white/[0.08] rounded-lg transition-all"
                      >
                        <Copy className="w-3 h-3" /> Copy
                      </button>
                    </div>
                  </div>
                  <div className="text-sm">{formatAnswer(answer)}</div>
                </div>
              )}
            </div>

            {/* Sidebar — desktop only */}
            <div className="hidden lg:block space-y-4">
              <div className="bg-white/[0.02] border border-white/[0.06] rounded-xl p-4">
                <h3 className="text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-3">Common Questions</h3>
                <div className="space-y-1">
                  {COMMON_QUESTIONS.map((q, i) => (
                    <button
                      key={i}
                      onClick={() => setQuestion(q)}
                      className="w-full text-left text-xs text-[#64748B] hover:text-[#94A3B8] py-2 px-3 rounded-lg hover:bg-white/[0.04] transition-all leading-relaxed"
                    >
                      {q}
                    </button>
                  ))}
                </div>
              </div>

              {history.length > 0 && (
                <div className="bg-white/[0.02] border border-white/[0.06] rounded-xl p-4">
                  <h3 className="text-xs font-semibold text-[#94A3B8] uppercase tracking-wider mb-3">Recent</h3>
                  <div className="space-y-1">
                    {history.map((h, i) => (
                      <button
                        key={i}
                        onClick={() => { setQuestion(h.question); setAnswer(h.answer); }}
                        className="w-full text-left text-xs text-[#64748B] hover:text-[#94A3B8] py-2 px-3 rounded-lg hover:bg-white/[0.04] transition-all leading-relaxed line-clamp-2"
                      >
                        {h.question}
                      </button>
                    ))}
                  </div>
                </div>
              )}
            </div>
          </div>
        </div>
      </main>
    </div>
  );
}
