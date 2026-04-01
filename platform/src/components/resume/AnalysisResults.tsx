'use client';

import { useState } from 'react';
import { motion } from 'framer-motion';
import {
  CheckCircle,
  XCircle,
  Copy,
  Check,
  TrendingUp,
  AlertTriangle,
  Lightbulb,
  Target,
} from 'lucide-react';
import toast from 'react-hot-toast';
import type { AnalysisResult } from '@/types';
import { scoreColor, getScoreLabel } from '@/lib/utils';
import Badge from '@/components/ui/Badge';

interface AnalysisResultsProps {
  result: AnalysisResult;
}

export default function AnalysisResults({ result }: AnalysisResultsProps) {
  const [copiedBullet, setCopiedBullet] = useState<number | null>(null);
  const [copiedAll, setCopiedAll] = useState(false);

  const circumference = 2 * Math.PI * 45;
  const color = scoreColor(result.score);
  const label = getScoreLabel(result.score);

  const handleCopyBullet = async (text: string, index: number) => {
    await navigator.clipboard.writeText(text);
    setCopiedBullet(index);
    setTimeout(() => setCopiedBullet(null), 2000);
    toast.success('Copied to clipboard!');
  };

  const handleCopyAll = async () => {
    const text = [
      `=== RESUME ANALYSIS RESULTS ===`,
      `Overall Score: ${result.score}/100`,
      `ATS Score: ${result.atsScore}/100`,
      ``,
      `=== MISSING KEYWORDS ===`,
      result.missingKeywords.join(', '),
      ``,
      `=== SKILL GAPS ===`,
      result.skillGaps.join(', '),
      ``,
      `=== SUGGESTIONS ===`,
      result.suggestions.map((s, i) => `${i + 1}. ${s}`).join('\n'),
      ``,
      `=== IMPROVED BULLET POINTS ===`,
      result.improvedBullets.map((b, i) => `${i + 1}. ${b}`).join('\n'),
    ].join('\n');

    await navigator.clipboard.writeText(text);
    setCopiedAll(true);
    setTimeout(() => setCopiedAll(false), 2000);
    toast.success('All results copied!');
  };

  return (
    <motion.div
      initial={{ opacity: 0, y: 20 }}
      animate={{ opacity: 1, y: 0 }}
      transition={{ duration: 0.5 }}
      className="space-y-5"
    >
      {/* Header with scores */}
      <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-6">
        <div className="flex items-center justify-between mb-6">
          <h2 className="text-base font-semibold text-[#F8FAFC]">Analysis Results</h2>
          <button
            onClick={handleCopyAll}
            className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium text-[#94A3B8] hover:text-white bg-white/5 hover:bg-white/10 border border-white/10 rounded-lg transition-all"
          >
            {copiedAll ? <Check className="w-3.5 h-3.5 text-[#22C55E]" /> : <Copy className="w-3.5 h-3.5" />}
            {copiedAll ? 'Copied!' : 'Copy All'}
          </button>
        </div>

        <div className="flex flex-col sm:flex-row items-center gap-8">
          {/* Main Score Ring */}
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
                stroke={color}
                strokeWidth="8"
                strokeLinecap="round"
                strokeDasharray={circumference}
                initial={{ strokeDashoffset: circumference }}
                animate={{
                  strokeDashoffset: circumference * (1 - result.score / 100),
                }}
                transition={{ duration: 1.5, ease: 'easeOut' }}
                style={{ filter: `drop-shadow(0 0 6px ${color}60)` }}
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
              <span className="text-xs text-[#94A3B8] mt-0.5">Match Score</span>
              <span className="text-xs font-semibold mt-0.5" style={{ color }}>
                {label}
              </span>
            </div>
          </div>

          {/* ATS + other metrics */}
          <div className="flex-1 w-full space-y-4">
            <div>
              <div className="flex justify-between text-sm mb-1.5">
                <div className="flex items-center gap-1.5">
                  <Target className="w-3.5 h-3.5 text-[#2563EB]" />
                  <span className="text-[#CBD5E1]">ATS Score</span>
                </div>
                <span className="text-[#F8FAFC] font-semibold">{result.atsScore}%</span>
              </div>
              <div className="h-2 bg-white/[0.06] rounded-full overflow-hidden">
                <motion.div
                  className="h-full rounded-full bg-[#2563EB]"
                  initial={{ width: 0 }}
                  animate={{ width: `${result.atsScore}%` }}
                  transition={{ duration: 1, delay: 0.3, ease: 'easeOut' }}
                />
              </div>
            </div>

            {/* Weak sections summary */}
            {result.weakSections?.length > 0 && (
              <div className="p-3 bg-[#F59E0B]/10 border border-[#F59E0B]/20 rounded-lg">
                <div className="flex items-center gap-2 mb-1">
                  <AlertTriangle className="w-3.5 h-3.5 text-[#F59E0B]" />
                  <span className="text-xs font-medium text-[#FCD34D]">Weak Sections</span>
                </div>
                <p className="text-xs text-[#CBD5E1]">
                  {result.weakSections.join(', ')}
                </p>
              </div>
            )}
          </div>
        </div>
      </div>

      {/* Missing Keywords */}
      {result.missingKeywords?.length > 0 && (
        <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-6">
          <div className="flex items-center gap-2 mb-4">
            <XCircle className="w-[18px] h-[18px] text-[#EF4444]" />
            <h3 className="text-sm font-semibold text-[#F8FAFC]">Missing Keywords</h3>
            <span className="text-xs text-[#94A3B8]">({result.missingKeywords.length} keywords not found)</span>
          </div>
          <div className="flex flex-wrap gap-2">
            {result.missingKeywords.map((kw) => (
              <Badge key={kw} variant="danger">
                {kw}
              </Badge>
            ))}
          </div>
          <p className="mt-3 text-xs text-[#94A3B8]">
            Add these keywords naturally throughout your resume to improve your ATS score.
          </p>
        </div>
      )}

      {/* Skill Gaps */}
      {result.skillGaps?.length > 0 && (
        <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-6">
          <div className="flex items-center gap-2 mb-4">
            <TrendingUp className="w-[18px] h-[18px] text-[#F59E0B]" />
            <h3 className="text-sm font-semibold text-[#F8FAFC]">Skill Gaps</h3>
          </div>
          <div className="flex flex-wrap gap-2">
            {result.skillGaps.map((skill) => (
              <Badge key={skill} variant="warning">
                {skill}
              </Badge>
            ))}
          </div>
        </div>
      )}

      {/* Suggestions */}
      {result.suggestions?.length > 0 && (
        <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-6">
          <div className="flex items-center gap-2 mb-4">
            <Lightbulb className="w-[18px] h-[18px] text-[#F97316]" />
            <h3 className="text-sm font-semibold text-[#F8FAFC]">Improvement Suggestions</h3>
          </div>
          <div className="space-y-3">
            {result.suggestions.map((suggestion, i) => (
              <motion.div
                key={i}
                initial={{ opacity: 0, x: -10 }}
                animate={{ opacity: 1, x: 0 }}
                transition={{ duration: 0.3, delay: i * 0.05 }}
                className="flex items-start gap-3 p-3 bg-white/[0.03] rounded-lg border border-white/[0.06]"
              >
                <div className="w-5 h-5 rounded-full bg-[#F97316]/20 flex items-center justify-center shrink-0 mt-0.5">
                  <span className="text-[10px] font-bold text-[#F97316]">{i + 1}</span>
                </div>
                <p className="text-sm text-[#CBD5E1] leading-relaxed">{suggestion}</p>
              </motion.div>
            ))}
          </div>
        </div>
      )}

      {/* Improved Bullet Points */}
      {result.improvedBullets?.length > 0 && (
        <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-6">
          <div className="flex items-center gap-2 mb-4">
            <CheckCircle className="w-[18px] h-[18px] text-[#22C55E]" />
            <h3 className="text-sm font-semibold text-[#F8FAFC]">Improved Bullet Points</h3>
          </div>
          <p className="text-xs text-[#94A3B8] mb-4">
            Copy and use these AI-optimized bullet points in your resume:
          </p>
          <div className="space-y-3">
            {result.improvedBullets.map((bullet, i) => (
              <motion.div
                key={i}
                initial={{ opacity: 0, y: 8 }}
                animate={{ opacity: 1, y: 0 }}
                transition={{ duration: 0.3, delay: i * 0.06 }}
                className="group relative flex items-start gap-3 p-3 bg-[#22C55E]/[0.05] rounded-lg border border-[#22C55E]/10 hover:border-[#22C55E]/20 transition-all"
              >
                <CheckCircle className="w-4 h-4 text-[#22C55E] shrink-0 mt-0.5" />
                <p className="text-sm text-[#CBD5E1] leading-relaxed flex-1 pr-8">{bullet}</p>
                <button
                  onClick={() => handleCopyBullet(bullet, i)}
                  className="absolute right-3 top-3 p-1 text-[#94A3B8] hover:text-white opacity-60 group-hover:opacity-100 transition-all bg-white/10 rounded"
                  title="Copy bullet point"
                >
                  {copiedBullet === i ? (
                    <Check className="w-3.5 h-3.5 text-[#22C55E]" />
                  ) : (
                    <Copy className="w-3.5 h-3.5" />
                  )}
                </button>
              </motion.div>
            ))}
          </div>
        </div>
      )}
    </motion.div>
  );
}
