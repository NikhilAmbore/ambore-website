'use client';

import { useState, useEffect, useCallback } from 'react';
import { Search, SlidersHorizontal, X, ChevronLeft, ChevronRight } from 'lucide-react';
import type { Job } from '@/types';
import JobCard from './JobCard';
import LoadingSpinner from '@/components/ui/LoadingSpinner';
import { useDebounce } from 'use-debounce';

const JOB_TYPES = ['Full-time', 'Part-time', 'Contract', 'Internship'];
const LOCATIONS = ['Remote', 'New York, NY', 'San Francisco, CA', 'Austin, TX', 'Seattle, WA', 'Boston, MA'];
const LIMIT = 20;

export default function JobList() {
  const [jobs, setJobs] = useState<Job[]>([]);
  const [total, setTotal] = useState(0);
  const [pages, setPages] = useState(1);
  const [loading, setLoading] = useState(true);
  const [search, setSearch] = useState('');
  const [typeFilter, setTypeFilter] = useState('');
  const [remoteFilter, setRemoteFilter] = useState<boolean | undefined>(undefined);
  const [locationFilter, setLocationFilter] = useState('');
  const [showFilters, setShowFilters] = useState(false);
  const [currentPage, setCurrentPage] = useState(1);

  const [debouncedSearch] = useDebounce(search, 400);

  const fetchJobs = useCallback(async () => {
    setLoading(true);
    try {
      const params = new URLSearchParams({ page: String(currentPage), limit: String(LIMIT) });
      if (debouncedSearch) params.set('search', debouncedSearch);
      if (typeFilter) params.set('type', typeFilter);
      if (remoteFilter !== undefined) params.set('remote', String(remoteFilter));
      if (locationFilter) params.set('location', locationFilter);

      const res = await fetch(`/api/jobs?${params}`);
      const data = await res.json();
      setJobs(data.data ?? []);
      setTotal(data.total ?? 0);
      setPages(data.pages ?? 1);
    } catch {
      setJobs([]);
    } finally {
      setLoading(false);
    }
  }, [currentPage, debouncedSearch, typeFilter, remoteFilter, locationFilter]);

  useEffect(() => {
    fetchJobs();
  }, [fetchJobs]);

  // Reset to page 1 when filters change
  useEffect(() => {
    setCurrentPage(1);
  }, [debouncedSearch, typeFilter, remoteFilter, locationFilter]);

  const clearFilters = () => {
    setSearch('');
    setTypeFilter('');
    setRemoteFilter(undefined);
    setLocationFilter('');
    setCurrentPage(1);
  };

  const hasActiveFilters = search || typeFilter || remoteFilter !== undefined || locationFilter;

  // Pagination: show up to 7 page buttons centered around current
  const pageButtons = (() => {
    if (pages <= 7) return Array.from({ length: pages }, (_, i) => i + 1);
    const half = 3;
    let start = Math.max(1, currentPage - half);
    let end = Math.min(pages, currentPage + half);
    if (currentPage - half < 1) end = Math.min(pages, end + (half - (currentPage - 1)));
    if (currentPage + half > pages) start = Math.max(1, start - (half - (pages - currentPage)));
    return Array.from({ length: end - start + 1 }, (_, i) => start + i);
  })();

  return (
    <div className="flex flex-col lg:flex-row gap-6">
      {/* Filter Sidebar */}
      <div className={`lg:w-56 shrink-0 ${showFilters ? 'block' : 'hidden lg:block'}`}>
        <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-5 sticky top-4">
          <div className="flex items-center justify-between mb-4">
            <h3 className="text-sm font-semibold text-[#F8FAFC]">Filters</h3>
            {hasActiveFilters && (
              <button onClick={clearFilters} className="text-xs text-[#F97316] hover:text-[#FB923C] transition-colors">
                Clear all
              </button>
            )}
          </div>

          <div className="mb-5">
            <p className="text-xs font-medium text-[#94A3B8] uppercase tracking-wider mb-2">Job Type</p>
            <div className="space-y-1.5">
              {JOB_TYPES.map(type => (
                <label key={type} className="flex items-center gap-2.5 cursor-pointer group">
                  <input
                    type="radio"
                    name="jobType"
                    checked={typeFilter === type}
                    onChange={() => setTypeFilter(prev => prev === type ? '' : type)}
                    className="w-3.5 h-3.5 accent-[#F97316]"
                  />
                  <span className="text-sm text-[#94A3B8] group-hover:text-[#F8FAFC] transition-colors">{type}</span>
                </label>
              ))}
            </div>
          </div>

          <div className="mb-5">
            <p className="text-xs font-medium text-[#94A3B8] uppercase tracking-wider mb-2">Work Mode</p>
            <div className="space-y-1.5">
              {[{ label: 'Remote', value: true }, { label: 'On-site', value: false }].map(opt => (
                <label key={opt.label} className="flex items-center gap-2.5 cursor-pointer group">
                  <input
                    type="radio"
                    name="remote"
                    checked={remoteFilter === opt.value}
                    onChange={() => setRemoteFilter(prev => prev === opt.value ? undefined : opt.value)}
                    className="w-3.5 h-3.5 accent-[#F97316]"
                  />
                  <span className="text-sm text-[#94A3B8] group-hover:text-[#F8FAFC] transition-colors">{opt.label}</span>
                </label>
              ))}
            </div>
          </div>

          <div>
            <p className="text-xs font-medium text-[#94A3B8] uppercase tracking-wider mb-2">Location</p>
            <div className="space-y-1.5">
              {LOCATIONS.map(loc => (
                <label key={loc} className="flex items-center gap-2.5 cursor-pointer group">
                  <input
                    type="radio"
                    name="location"
                    checked={locationFilter === loc}
                    onChange={() => setLocationFilter(prev => prev === loc ? '' : loc)}
                    className="w-3.5 h-3.5 accent-[#F97316]"
                  />
                  <span className="text-sm text-[#94A3B8] group-hover:text-[#F8FAFC] transition-colors truncate">{loc}</span>
                </label>
              ))}
            </div>
          </div>
        </div>
      </div>

      {/* Main Content */}
      <div className="flex-1 min-w-0">
        <div className="flex gap-3 mb-6">
          <div className="relative flex-1">
            <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-[#94A3B8]" />
            <input
              type="text"
              value={search}
              onChange={e => setSearch(e.target.value)}
              placeholder="Search jobs, companies, skills..."
              className="w-full h-10 pl-10 pr-4 bg-white/[0.04] border border-white/10 rounded-lg text-sm text-[#F8FAFC] placeholder:text-[#475569] focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
            />
            {search && (
              <button onClick={() => setSearch('')} className="absolute right-3 top-1/2 -translate-y-1/2 text-[#94A3B8] hover:text-white">
                <X className="w-4 h-4" />
              </button>
            )}
          </div>
          <button
            onClick={() => setShowFilters(!showFilters)}
            className={`lg:hidden flex items-center gap-2 h-10 px-4 rounded-lg text-sm font-medium border transition-all ${
              showFilters || hasActiveFilters
                ? 'bg-[#F97316]/10 border-[#F97316]/20 text-[#FB923C]'
                : 'bg-white/[0.04] border-white/10 text-[#94A3B8] hover:text-white'
            }`}
          >
            <SlidersHorizontal className="w-4 h-4" />
            Filters
          </button>
        </div>

        <p className="text-sm text-[#94A3B8] mb-4">
          {loading ? 'Loading...' : `${total.toLocaleString()} jobs found`}
          {hasActiveFilters && (
            <button onClick={clearFilters} className="ml-2 text-[#F97316] hover:text-[#FB923C] text-xs">
              Clear filters ×
            </button>
          )}
        </p>

        {loading ? (
          <div className="flex items-center justify-center py-20">
            <LoadingSpinner size="lg" color="#F97316" />
          </div>
        ) : jobs.length === 0 ? (
          <div className="text-center py-20">
            <p className="text-[#94A3B8] text-base mb-2">No jobs match your filters</p>
            <p className="text-[#94A3B8] text-sm">Try adjusting your search or clearing filters</p>
          </div>
        ) : (
          <div className="grid grid-cols-1 xl:grid-cols-2 gap-4">
            {jobs.map(job => <JobCard key={job.id} job={job} />)}
          </div>
        )}

        {pages > 1 && (
          <div className="flex items-center justify-center gap-2 mt-8">
            <button
              onClick={() => setCurrentPage(p => Math.max(1, p - 1))}
              disabled={currentPage === 1}
              className="p-2 rounded-lg text-[#94A3B8] hover:text-white hover:bg-white/10 disabled:opacity-40 disabled:cursor-not-allowed border border-white/10 transition-all"
            >
              <ChevronLeft className="w-4 h-4" />
            </button>
            {pageButtons.map(page => (
              <button
                key={page}
                onClick={() => setCurrentPage(page)}
                className={`w-9 h-9 rounded-lg text-sm font-medium transition-all border ${
                  currentPage === page
                    ? 'bg-[#F97316] border-[#F97316] text-white'
                    : 'bg-white/[0.04] border-white/10 text-[#94A3B8] hover:text-white hover:bg-white/10'
                }`}
              >
                {page}
              </button>
            ))}
            <button
              onClick={() => setCurrentPage(p => Math.min(pages, p + 1))}
              disabled={currentPage === pages}
              className="p-2 rounded-lg text-[#94A3B8] hover:text-white hover:bg-white/10 disabled:opacity-40 disabled:cursor-not-allowed border border-white/10 transition-all"
            >
              <ChevronRight className="w-4 h-4" />
            </button>
          </div>
        )}
      </div>
    </div>
  );
}
