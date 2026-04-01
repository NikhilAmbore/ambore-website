'use client';

import { useState } from 'react';
import { MapPin, Building2, DollarSign, ExternalLink, Bookmark, BookmarkCheck, Sparkles } from 'lucide-react';
import type { Job } from '@/types';
import Badge from '@/components/ui/Badge';
import { formatDate, truncate } from '@/lib/utils';
import { useRouter } from 'next/navigation';
import toast from 'react-hot-toast';

interface JobCardProps {
  job: Job;
  isSaved?: boolean;
}

export default function JobCard({ job, isSaved = false }: JobCardProps) {
  const router = useRouter();
  const [saved, setSaved] = useState(isSaved);
  const [saving, setSaving] = useState(false);

  const handleSave = async (e: React.MouseEvent) => {
    e.stopPropagation();
    if (saving) return;
    setSaving(true);
    const next = !saved;
    setSaved(next);
    try {
      const res = await fetch('/api/jobs/save', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          jobId: job.id,
          action: next ? 'save' : 'unsave',
          jobData: { title: job.title, company: job.company, url: job.url },
        }),
      });
      if (!res.ok) {
        setSaved(!next);
        toast.error('Failed to save job');
      } else {
        toast.success(next ? 'Job saved!' : 'Removed from saved');
      }
    } catch {
      setSaved(!next);
      toast.error('Failed to save job');
    } finally {
      setSaving(false);
    }
  };

  const handleAnalyze = (e: React.MouseEvent) => {
    e.stopPropagation();
    const params = new URLSearchParams({ jobDescription: job.description.slice(0, 2000) });
    router.push(`/resume?${params.toString()}`);
  };

  const companyInitials = job.company.split(' ').map((w) => w[0]).join('').toUpperCase().slice(0, 2);

  return (
    <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-5 hover:bg-white/[0.06] hover:border-white/[0.15] transition-all group">
      {/* Header */}
      <div className="flex items-start justify-between gap-3 mb-4">
        <div className="flex items-center gap-3 min-w-0">
          <div className="w-10 h-10 rounded-lg bg-gradient-to-br from-white/10 to-white/5 border border-white/10 flex items-center justify-center text-sm font-bold text-[#CBD5E1] shrink-0">
            {companyInitials}
          </div>
          <div className="min-w-0">
            <h3 className="text-sm font-semibold text-[#F8FAFC] truncate group-hover:text-white transition-colors">
              {job.title}
            </h3>
            <div className="flex items-center gap-1.5 text-xs text-[#94A3B8] mt-0.5">
              <Building2 className="w-3 h-3 shrink-0" />
              <span className="truncate">{job.company}</span>
            </div>
          </div>
        </div>

        <button
          onClick={handleSave}
          disabled={saving}
          className={`p-1.5 rounded-lg transition-all shrink-0 ${
            saved
              ? 'text-[#F97316] bg-[#F97316]/10 hover:bg-[#F97316]/20'
              : 'text-[#94A3B8] hover:text-[#F97316] hover:bg-[#F97316]/10'
          }`}
          title={saved ? 'Remove from saved' : 'Save job'}
        >
          {saved ? <BookmarkCheck className="w-4 h-4" /> : <Bookmark className="w-4 h-4" />}
        </button>
      </div>

      {/* Meta */}
      <div className="flex flex-wrap gap-3 mb-4 text-xs text-[#94A3B8]">
        <div className="flex items-center gap-1">
          <MapPin className="w-3 h-3" />
          <span>{job.location}</span>
        </div>
        {job.salary && (
          <div className="flex items-center gap-1">
            <DollarSign className="w-3 h-3" />
            <span>{job.salary}</span>
          </div>
        )}
      </div>

      {/* Badges */}
      <div className="flex flex-wrap gap-1.5 mb-4">
        <Badge variant={job.remote ? 'success' : 'default'} size="sm">
          {job.remote ? 'Remote' : 'On-site'}
        </Badge>
        <Badge variant="info" size="sm">
          {job.type}
        </Badge>
        {job.tags.slice(0, 2).map((tag) => (
          <Badge key={tag} variant="default" size="sm">
            {tag}
          </Badge>
        ))}
      </div>

      {/* Description */}
      <p className="text-xs text-[#94A3B8] leading-relaxed mb-4">
        {truncate(job.description, 120)}
      </p>

      {/* Footer */}
      <div className="flex items-center justify-between pt-4 border-t border-white/[0.06]">
        <span className="text-xs text-[#94A3B8]">{formatDate(job.postedAt)}</span>
        <div className="flex items-center gap-2">
          <button
            onClick={handleAnalyze}
            className="flex items-center gap-1.5 h-7 px-3 text-xs font-medium text-[#FB923C] bg-[#F97316]/10 hover:bg-[#F97316]/20 border border-[#F97316]/20 rounded-lg transition-all"
          >
            <Sparkles className="w-3 h-3" />
            Analyze
          </button>
          <a
            href={job.url}
            target="_blank"
            rel="noopener noreferrer"
            onClick={(e) => e.stopPropagation()}
            className="flex items-center gap-1.5 h-7 px-3 text-xs font-medium text-[#94A3B8] hover:text-white bg-white/5 hover:bg-white/10 border border-white/10 rounded-lg transition-all"
          >
            Apply
            <ExternalLink className="w-3 h-3" />
          </a>
        </div>
      </div>
    </div>
  );
}
