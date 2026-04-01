import { NextRequest, NextResponse } from 'next/server';
import { promises as fs } from 'fs';
import path from 'path';
import type { Job } from '@/types';

interface RawJob {
  id: string;
  title: string;
  company: string;
  location: string;
  description: string;
  is_remote: boolean;
  is_usa: boolean;
  url: string;
  salary?: string | null;
  job_type?: string | null;
  date_posted?: string | null;
  tags?: string[] | null;
}

let cachedJobs: Job[] | null = null;

async function loadJobs(): Promise<Job[]> {
  if (cachedJobs) return cachedJobs;

  // Try multiple paths: local dev (sibling backend dir) or production (public folder)
  const candidates = [
    path.resolve(process.cwd(), '..', 'backend', 'jobs.json'),
    path.resolve(process.cwd(), 'public', 'jobs.json'),
    path.resolve(process.cwd(), 'jobs.json'),
  ];

  let raw: string | null = null;
  for (const p of candidates) {
    try {
      raw = await fs.readFile(p, 'utf-8');
      break;
    } catch {
      // try next
    }
  }

  if (!raw) {
    cachedJobs = [];
    return cachedJobs;
  }

  let data: RawJob[];
  try {
    data = JSON.parse(raw);
  } catch (e) {
    console.error('Failed to parse jobs.json:', e);
    cachedJobs = [];
    return cachedJobs;
  }

  cachedJobs = data
    .filter(j => j.is_usa !== false)
    .map(j => ({
      id: j.id,
      title: j.title,
      company: j.company,
      location: j.location || (j.is_remote ? 'Remote' : 'USA'),
      description: j.description ?? '',
      salary: j.salary ?? null,
      type: j.job_type ?? 'Full-time',
      remote: j.is_remote ?? false,
      url: j.url,
      postedAt: j.date_posted ? new Date(j.date_posted) : new Date(),
      tags: j.tags ?? [],
    }));

  return cachedJobs;
}

export async function GET(request: NextRequest) {
  try {
    const { searchParams } = new URL(request.url);
    const search = searchParams.get('search')?.toLowerCase().trim() ?? '';
    const type = searchParams.get('type')?.toLowerCase() ?? '';
    const remoteParam = searchParams.get('remote');
    const location = searchParams.get('location')?.toLowerCase() ?? '';
    const page = Math.max(1, parseInt(searchParams.get('page') ?? '1', 10));
    const limit = Math.min(50, Math.max(1, parseInt(searchParams.get('limit') ?? '20', 10)));

    let jobs = await loadJobs();

    if (search) {
      jobs = jobs.filter(
        j =>
          j.title.toLowerCase().includes(search) ||
          j.company.toLowerCase().includes(search) ||
          j.location.toLowerCase().includes(search) ||
          j.tags.some(t => t.toLowerCase().includes(search))
      );
    }

    if (type) {
      jobs = jobs.filter(j => j.type.toLowerCase().includes(type));
    }

    if (remoteParam !== null) {
      const isRemote = remoteParam === 'true';
      jobs = jobs.filter(j => j.remote === isRemote);
    }

    if (location) {
      jobs = jobs.filter(
        j =>
          j.location.toLowerCase().includes(location) ||
          (location === 'remote' && j.remote)
      );
    }

    const total = jobs.length;
    const start = (page - 1) * limit;
    const paginated = jobs.slice(start, start + limit);

    return NextResponse.json({
      success: true,
      data: paginated,
      total,
      page,
      pages: Math.ceil(total / limit),
    });
  } catch (error) {
    console.error('Jobs API error:', error);
    return NextResponse.json({ error: 'Failed to fetch jobs' }, { status: 500 });
  }
}
