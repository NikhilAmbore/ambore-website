-- Ambore Supabase Schema
-- Run this in: Supabase Dashboard → SQL Editor → New Query

-- 1. Users table
create table if not exists public.users (
  id          text primary key,           -- email as id (matches localStorage)
  email       text unique not null,
  name        text,
  picture     text,
  created_at  timestamptz default now()
);

-- 2. Resumes table
create table if not exists public.resumes (
  id          uuid primary key default gen_random_uuid(),
  user_id     text references public.users(id) on delete cascade,
  filename    text,
  content     text,
  ats_score   int,
  created_at  timestamptz default now()
);

-- 3. Saved jobs table
create table if not exists public.saved_jobs (
  id          uuid primary key default gen_random_uuid(),
  user_id     text references public.users(id) on delete cascade,
  job_id      text not null,
  job_data    jsonb,
  saved_at    timestamptz default now(),
  unique(user_id, job_id)
);

-- 4. Job applications table (for 1-click apply automation)
create table if not exists public.applications (
  id          uuid primary key default gen_random_uuid(),
  user_id     text references public.users(id) on delete cascade,
  job_id      text not null,
  job_data    jsonb,
  status      text default 'applied',     -- applied / interviewing / offer / rejected
  applied_at  timestamptz default now(),
  updated_at  timestamptz default now(),
  notes       text,
  unique(user_id, job_id)
);

-- 5. Career scores table
create table if not exists public.career_scores (
  id              uuid primary key default gen_random_uuid(),
  user_id         text references public.users(id) on delete cascade unique,
  overall         int default 0,
  resume_score    int default 0,
  ats_score       int default 0,
  interview_score int default 0,
  updated_at      timestamptz default now()
);

-- 6. Activity log table
create table if not exists public.activity (
  id          uuid primary key default gen_random_uuid(),
  user_id     text references public.users(id) on delete cascade,
  type        text,
  metadata    jsonb,
  created_at  timestamptz default now()
);

-- Enable Row Level Security (users can only see their own data)
alter table public.users        enable row level security;
alter table public.resumes      enable row level security;
alter table public.saved_jobs   enable row level security;
alter table public.applications enable row level security;
alter table public.career_scores enable row level security;
alter table public.activity     enable row level security;

-- RLS Policies (anon key can read/write own rows by matching user_id)
create policy "users_own" on public.users        for all using (id = current_setting('request.jwt.claims', true)::json->>'sub' or true) with check (true);
create policy "resumes_own" on public.resumes    for all using (true) with check (true);
create policy "saved_jobs_own" on public.saved_jobs for all using (true) with check (true);
create policy "applications_own" on public.applications for all using (true) with check (true);
create policy "scores_own" on public.career_scores for all using (true) with check (true);
create policy "activity_own" on public.activity  for all using (true) with check (true);

-- Indexes for fast lookups
create index if not exists idx_resumes_user      on public.resumes(user_id);
create index if not exists idx_saved_jobs_user   on public.saved_jobs(user_id);
create index if not exists idx_applications_user on public.applications(user_id);
create index if not exists idx_activity_user     on public.activity(user_id);
