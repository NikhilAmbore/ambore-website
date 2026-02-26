# Ambore — Full-Stack AI Career Platform
### Project Documentation · From Scratch to Deployment

---

## Table of Contents

1. [Project Overview](#1-project-overview)
2. [Problem Statement](#2-problem-statement)
3. [Architecture Overview](#3-architecture-overview)
4. [Technology Stack](#4-technology-stack)
5. [Frontend — Pages & Features](#5-frontend--pages--features)
6. [Backend — FastAPI REST API](#6-backend--fastapi-rest-api)
7. [Database Design](#7-database-design)
8. [Job Scraping Engine](#8-job-scraping-engine)
9. [AI Features](#9-ai-features)
10. [Authentication System](#10-authentication-system)
11. [Analytics System](#11-analytics-system)
12. [API Reference](#12-api-reference)
13. [Deployment](#13-deployment)
14. [Live Statistics](#14-live-statistics)
15. [Project File Structure](#15-project-file-structure)

---

## 1. Project Overview

**Ambore** is a full-stack AI-powered career platform for tech and IT professionals. It aggregates real-time job listings from multiple public sources, provides an AI-driven resume builder, and an intelligent interview preparation co-pilot — all in one platform.

| Property | Value |
|---|---|
| **Live URL** | https://ambore.org |
| **Backend API** | https://web-production-d62ab.up.railway.app |
| **GitHub (Frontend)** | https://github.com/NikhilAmbore/ambore-website |
| **Status** | Live & Production |
| **Last scraped** | 2026-02-19 07:01 UTC |

---

## 2. Problem Statement

Job seekers in tech face three core pain points:

1. **Fragmented job listings** — jobs are scattered across USAJobs, Adzuna, Remotive, and niche boards. No single place aggregates them cleanly.
2. **Generic AI tools** — resume generators produce cookie-cutter output with no awareness of the job description or interview round.
3. **No structured interview prep** — candidates don't know how to answer behavioral vs technical questions using a proven framework.

**Ambore solves all three** by combining a live aggregated job board, a context-aware AI resume builder, and a round-specific interview co-pilot in one platform.

---

## 3. Architecture Overview

```
┌─────────────────────────────────────────────────────────┐
│                     USER BROWSER                        │
│                                                         │
│  index.html  ←→  jobs.html  ←→  job-detail.html        │
│  resume.html ←→  app.html (Interview Co-pilot)          │
│                                                         │
│  Auth: localStorage  │  AI: Claude API (direct fetch)   │
└──────────┬──────────────────────────────────────────────┘
           │  REST API (HTTPS)
           ▼
┌─────────────────────────────────────────────────────────┐
│              RAILWAY — FastAPI Backend                  │
│                                                         │
│  main.py  →  crud.py  →  models.py  →  database.py     │
│  scheduler.py  →  scrapers/  →  PostgreSQL              │
│                                                         │
│  APScheduler fires daily at 2:00 AM EST                 │
│  5 scrapers pull fresh jobs → dedup → store             │
└──────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────┐
│              POSTGRESQL DATABASE (Railway)              │
│                                                         │
│  Table: jobs         (job listings, full-text search)   │
│  Table: analytics    (page views, feature usage)        │
└─────────────────────────────────────────────────────────┘

External APIs used:
  ├── USAJobs API (federal government jobs)
  ├── Adzuna API (aggregated job board)
  ├── The Muse API (company culture + jobs)
  ├── Remotive API (remote-only tech jobs)
  ├── Apify Google Jobs Actor (Google job search results)
  └── Anthropic Claude API (AI resume + interview prep)
```

---

## 4. Technology Stack

### Frontend
| Layer | Technology |
|---|---|
| Language | HTML5, CSS3, Vanilla JavaScript (ES6+) |
| Fonts | Google Fonts (Inter) |
| AI Streaming | Native `fetch()` with `ReadableStream` (Server-Sent Events) |
| Auth | `localStorage` (client-side session) |
| Deploy | Netlify (auto-deploy from GitHub `main` branch) |

### Backend
| Layer | Technology |
|---|---|
| Framework | FastAPI 0.109+ |
| Language | Python 3.11 |
| ORM | SQLAlchemy 2.0 |
| Database | PostgreSQL (Railway managed) |
| Validation | Pydantic v2 |
| Scheduler | APScheduler 3.10 (CronTrigger) |
| HTTP Client | HTTPX |
| Server | Uvicorn (ASGI) |
| Deploy | Railway (Nixpacks build) |

### AI
| Component | Technology |
|---|---|
| Model | `claude-haiku-4-5-20251001` (Anthropic) |
| Invocation | Direct browser `fetch()` to Anthropic API |
| Streaming | `text/event-stream` with chunked response parsing |

---

## 5. Frontend — Pages & Features

The frontend is a **zero-framework, pure HTML/CSS/JS** multi-page application. Five pages, each serving a distinct purpose.

### 5.1 `index.html` — Homepage

The entry point and marketing page. Contains:

- **Hero section** — value proposition and CTA buttons (gated behind login)
- **Features grid** — Jobs, Resume Builder, Interview Co-pilot cards
- **Auth modal** — Login and Sign Up modal dialog
- **Navigation** — All feature links call `goToFeature(page)` to enforce auth

**Auth gate pattern:**
```javascript
// All feature buttons use this instead of direct href
function goToFeature(page) {
  if (getSession()) { window.location.href = page; return; }
  _pendingRedirect = page;   // remember where user wanted to go
  openAuthModal('login');
}

// After successful login, redirect to intended page
function handleLogin() {
  saveSession(user);
  closeAuthModal();
  if (_pendingRedirect) { window.location.href = _pendingRedirect; return; }
  updateNavState();
}
```

**Auto-open modal from redirect:**
```javascript
// When redirected from a gated page, open modal automatically
// URL: index.html?auth=login&redirect=jobs.html&msg=Please+log+in
let _pendingRedirect = null;
(function() {
  const params = new URLSearchParams(window.location.search);
  if (params.get('auth')) {
    _pendingRedirect = params.get('redirect') || null;
    openAuthModal(params.get('auth'));
  }
})();
```

---

### 5.2 `jobs.html` — Job Board

Real-time job listings pulled from the backend API. Features:

- **Search bar** — full-text search (PostgreSQL `tsvector` powered)
- **Filters panel** — Category, State, Work Type (Remote/Hybrid/Onsite), Experience Level, Salary, Posted Within, Source
- **Paginated results** — 20 jobs per page with next/prev navigation
- **Job cards** — title, company, location, work type badge, salary, source badge, "View Details" button
- **Sort** — by Date Posted or Salary

**Auth guard** (first script in `<body>`):
```javascript
(function() {
  var s = JSON.parse(localStorage.getItem('ambore_user') || 'null');
  if (!s || (s.expiresAt && Date.now() > s.expiresAt)) {
    localStorage.removeItem('ambore_user');
    window.location.href = 'index.html?auth=login&redirect=jobs.html&msg=Please+log+in+to+browse+jobs';
  }
})();
```

**API call example:**
```javascript
const res = await fetch(
  `${API_BASE}/api/jobs?q=${query}&category=${cat}&work_type=${wt}&page=${page}&per_page=20`
);
const data = await res.json();
// data = { jobs: [...], total: 1377, page: 1, per_page: 20, total_pages: 69 }
```

---

### 5.3 `job-detail.html` — Job Detail Page

Full job description with apply button. Receives `?id=<UUID>` from jobs.html.

- Auth guarded (redirects to login if unauthenticated)
- Fetches single job: `GET /api/jobs/{job_id}`
- Displays full description, skills tags, salary range, company logo, source link
- "Apply Now" opens original job URL in new tab

---

### 5.4 `resume.html` — AI Resume Builder

Generates a professional, ATS-optimized resume from user inputs using Claude AI.

**Inputs collected:**
- Full name, email, phone, LinkedIn, GitHub
- Target role and company
- Work experience (freeform)
- Education
- Skills
- Job description to tailor toward

**How it works:**
1. User fills in the form
2. Clicks "Generate Resume"
3. A system prompt is constructed incorporating all fields + the target JD
4. Streamed request to Claude API (Haiku model)
5. Response streams into a live preview pane
6. User can copy/download the result

**Auth guard:** Redirects unauthenticated users to `index.html?auth=login&redirect=resume.html`

**Analytics:** `track('resume_start', 'resume')` fires each time a resume is generated.

---

### 5.5 `app.html` — Interview Co-pilot (AI)

The most sophisticated page. An AI interview preparation assistant that adapts to the interview round.

**Setup inputs:**
- Resume (pasted text)
- Job Description
- Target Role & Company
- Interview Round (Behavioral, Technical, Coding, System Design, etc.)

**Core intelligence — method selection:**

The system automatically detects which answer framework to use based on the selected round:

| Round Type | Framework | Description |
|---|---|---|
| Behavioral / 1st round | **STAR** | Situation → Task → Action → Result |
| Technical / Coding / System Design | **CAAR** | Challenge → Approach → Action → Result |

**System prompt logic:**
```javascript
function buildSystemPrompt() {
  const r = cfg.round.toLowerCase();
  const isCAAR = r.includes('coding') || r.includes('technical') ||
                 r.includes('system design') || r.includes('4th') ||
                 r.includes('5th') || r.includes('2nd') || r.includes('3rd');

  const base = `RESUME:\n${cfg.resume}\n\nJOB DESCRIPTION:\n${cfg.jd}
                \n\nROLE: ${cfg.role} at ${cfg.company}\nROUND: ${cfg.round}`;

  if (isCAAR) {
    return `${base}\n\nYou are Ambore AI. When the candidate gives an answer,
    respond ONLY with a polished CAAR-method paragraph:
    Challenge → Approach → Action → Result.
    One paragraph. No bullets. No coaching. No feedback.`;
  }
  return `${base}\n\nYou are Ambore AI. When the candidate gives an answer,
  respond ONLY with a polished STAR-method paragraph:
  Situation → Task → Action → Result.
  One paragraph. No bullets. No coaching. No feedback.`;
}
```

**Features:**
- Voice input (Web Speech API — `SpeechRecognition`)
- Text input
- Combined voice + text
- Streaming AI response via `ReadableStream`
- Round badge shows `⚙ CAAR` or `✦ STAR` after session starts
- Session config saved to `localStorage` for persistence

**Auth guard:** Redirects unauthenticated users to `index.html?auth=login&redirect=app.html`

---

## 6. Backend — FastAPI REST API

The backend is a **FastAPI** application deployed on Railway. All endpoints are documented at the `/docs` Swagger UI.

### Application Entry (`main.py`)

```python
@asynccontextmanager
async def lifespan(app: FastAPI):
    init_db()           # create tables if not exist
    scheduler = create_scheduler()
    scheduler.start()   # fires scrapers daily at 2AM EST
    yield
    scheduler.shutdown()
```

### CORS Configuration

Allows requests from:
- `https://ambore.org`
- `https://incandescent-frangollo-6b34b1.netlify.app` (Netlify preview)
- `http://localhost:3000`, `http://localhost:8080`, `http://127.0.0.1:5500` (local dev)

### Endpoints Summary

| Method | Path | Auth | Description |
|---|---|---|---|
| GET | `/` | Public | Health check |
| GET | `/api/jobs` | Public | Paginated job list with filters |
| GET | `/api/jobs/categories` | Public | All categories with counts |
| GET | `/api/jobs/locations` | Public | All states with counts |
| GET | `/api/jobs/{job_id}` | Public | Single job by UUID |
| GET | `/api/stats` | Public | Portal-wide statistics |
| POST | `/api/track` | Public | Record analytics event |
| POST | `/api/admin/scrape` | Admin key | Manually trigger scrape |
| GET | `/api/admin/scrape/status` | Admin key | Last scrape results |
| GET | `/api/admin/analytics` | Admin key | Usage analytics dashboard |

---

## 7. Database Design

### Table: `jobs`

| Column | Type | Description |
|---|---|---|
| `id` | UUID (PK) | Auto-generated unique identifier |
| `external_id` | VARCHAR(255) | Source-specific job ID |
| `title` | VARCHAR(500) | Job title |
| `company` | VARCHAR(300) | Company name |
| `location_city` | VARCHAR(200) | City |
| `location_state` | VARCHAR(100) | US State (full name) |
| `work_type` | VARCHAR(20) | `remote` / `hybrid` / `onsite` |
| `salary_min` | INTEGER | Min annual salary (USD) |
| `salary_max` | INTEGER | Max annual salary (USD) |
| `experience_level` | VARCHAR(50) | `entry` / `mid` / `senior` / `executive` |
| `category` | VARCHAR(100) | Auto-classified tech category |
| `skills` | TEXT[] | Array of skill tags |
| `description` | TEXT | Full job description |
| `apply_url` | TEXT | Link to original job posting |
| `company_logo` | TEXT | Logo image URL |
| `source` | VARCHAR(50) | `usajobs` / `adzuna` / `themuse` / `remotive` / `google_jobs` |
| `posted_at` | TIMESTAMP TZ | When the job was originally posted |
| `scraped_at` | TIMESTAMP TZ | When we scraped it |
| `expires_at` | TIMESTAMP TZ | Optional expiry date |
| `is_active` | BOOLEAN | `false` after 45 days |
| `search_vector` | TSVECTOR | PostgreSQL full-text search index |

**Unique constraint:** `(source, external_id)` — prevents duplicate inserts.

**Indexes:**
```sql
idx_jobs_source_external  (source, external_id) UNIQUE
idx_jobs_posted           (posted_at)
idx_jobs_category         (category)
idx_jobs_state            (location_state)
idx_jobs_active           (is_active)
idx_jobs_work_type        (work_type)
idx_jobs_search           (search_vector) USING GIN
```

### Table: `analytics`

| Column | Type | Description |
|---|---|---|
| `id` | INTEGER (PK) | Auto-increment |
| `event` | VARCHAR(50) | Event type: `page_view`, `login`, `signup`, `session_start`, `resume_start` |
| `page` | VARCHAR(100) | Page name: `index`, `jobs`, `app`, `resume`, `job_detail` |
| `created_at` | TIMESTAMP TZ | When the event occurred |

---

## 8. Job Scraping Engine

### Architecture

Each scraper inherits from `BaseScraper` and implements `fetch_jobs() → list[dict]`. The scheduler calls all 5 scrapers sequentially every day at 2:00 AM US Eastern time.

```
scheduler.py
    └── run_all_scrapers()
            ├── USAJobsScraper.fetch_jobs()
            ├── AdzunaScraper.fetch_jobs()
            ├── TheMuseScraper.fetch_jobs()
            ├── RemotiveScraper.fetch_jobs()
            └── ApifyGoogleJobsScraper.fetch_jobs()
                    ↓
            upsert_jobs_bulk(db, jobs)   # insert, skip dupes
            update_search_vectors(db)    # build tsvector
            expire_old_jobs(db, days=45) # deactivate old listings
```

### Base Scraper Intelligence

`BaseScraper` provides shared NLP-style classification:

**Category detection** — 18 regex rules match job titles/descriptions to categories:
```python
CATEGORY_RULES = [
  (r"(?i)\b(machine learning|ml engineer|ai engineer)\b", "AI & Machine Learning"),
  (r"(?i)\b(cyber|security|infosec|soc analyst)\b", "Cybersecurity"),
  (r"(?i)\b(devops|sre|site reliability|platform engineer)\b", "DevOps & Infrastructure"),
  # ... 15 more rules
]
```

**Experience level detection:**
```python
EXPERIENCE_RULES = [
  (r"(?i)\b(entry.level|junior|jr\.|associate|new grad)\b", "entry"),
  (r"(?i)\b(senior|sr\.|lead|staff|principal)\b", "senior"),
  # ...
]
```

**Work type detection:**
```python
WORK_TYPE_RULES = [
  (r"(?i)\b(remote|work from home|wfh|anywhere)\b", "remote"),
  (r"(?i)\b(hybrid|flexible|partly remote)\b", "hybrid"),
  (r"(?i)\b(on.?site|in.?office|in-person)\b", "onsite"),
]
```

**Salary parsing:**
```python
def parse_salary(self, salary_str: str) -> tuple[int, int]:
    numbers = re.findall(r'[\d,]+\.?\d*', salary_str)
    if re.search(r"(?i)(hour|hr|/hr)", salary_str):
        numbers = [n * 2080 for n in numbers]  # convert to annual
    return min(numbers), max(numbers)
```

### Scrapers

| Scraper | Source | Method | Jobs (current) |
|---|---|---|---|
| `USAJobsScraper` | USAJobs (federal) | REST API | 337 |
| `AdzunaScraper` | Adzuna | REST API | 1,000 |
| `TheMuseScraper` | The Muse | REST API | 1 |
| `RemotiveScraper` | Remotive | REST API | 19 |
| `ApifyGoogleJobsScraper` | Google Jobs (via Apify) | Apify Actor | 20 |

### Deduplication

Jobs are deduplicated at two levels:
1. **Database level:** `ON CONFLICT DO NOTHING` on `(source, external_id)` unique index
2. **Cross-source hashing:** `dedup_hash(title, company, location)` — MD5 hash for detecting same job posted across multiple boards

### Lifecycle

- Jobs are scraped fresh **every day at 2:00 AM EST**
- Jobs older than **45 days** are marked `is_active = False`
- APScheduler has a **1-hour grace period** — if the 2AM job is missed, it runs within 60 minutes

---

## 9. AI Features

### 9.1 Interview Co-pilot (`app.html`)

**Model:** `claude-haiku-4-5-20251001`

**How streaming works:**
```javascript
const response = await fetch('https://api.anthropic.com/v1/messages', {
  method: 'POST',
  headers: {
    'x-api-key': CLAUDE_API_KEY,
    'anthropic-version': '2023-06-01',
    'content-type': 'application/json',
    'anthropic-dangerous-direct-browser-access': 'true',
  },
  body: JSON.stringify({
    model: 'claude-haiku-4-5-20251001',
    max_tokens: 1024,
    stream: true,
    system: buildSystemPrompt(),
    messages: conversationHistory,
  })
});

const reader = response.body.getReader();
// Parse SSE chunks as they arrive
while (true) {
  const { done, value } = await reader.read();
  if (done) break;
  const text = new TextDecoder().decode(value);
  // Extract delta.text from each chunk and append to UI
}
```

**STAR Method** (behavioral rounds):
> Situation → Task → Action → Result
> One paragraph, no bullets, no coaching.

**CAAR Method** (technical/coding rounds):
> Challenge → Approach → Action → Result
> One paragraph, no bullets, no coaching.

The model receives the candidate's full resume, target job description, company, role, and round as context — so every answer is tailored to the actual position.

### 9.2 Resume Builder (`resume.html`)

**Model:** `claude-haiku-4-5-20251001`

The system prompt instructs Claude to produce a clean, ATS-optimized resume incorporating:
- The candidate's actual experience and education
- Keywords from the target job description
- Professional formatting using markdown (which renders in the preview pane)

---

## 10. Authentication System

Ambore uses a **client-side authentication** system built on `localStorage`. There is no server-side auth — users register/login through a modal that stores a session object locally.

**Session object:**
```javascript
{
  name: "Jane Doe",
  email: "jane@example.com",
  expiresAt: 1740000000000   // Unix ms, 7-day expiry
}
```

**Key functions:**
```javascript
function saveSession(user)  { localStorage.setItem('ambore_user', JSON.stringify(user)); }
function getSession()       { return JSON.parse(localStorage.getItem('ambore_user')); }
function clearSession()     { localStorage.removeItem('ambore_user'); }
```

**Session validation:**
```javascript
function isSessionValid(s) {
  return s && (!s.expiresAt || Date.now() < s.expiresAt);
}
```

**Auth-gated pages** — all three feature pages include this IIFE at the top of `<body>`:
```javascript
(function() {
  var s = JSON.parse(localStorage.getItem('ambore_user') || 'null');
  if (!s || (s.expiresAt && Date.now() > s.expiresAt)) {
    localStorage.removeItem('ambore_user');
    window.location.href = 'index.html?auth=login&redirect=PAGENAME.html&msg=...';
  }
})();
```

This runs **before any content renders**, ensuring unauthenticated users are always redirected.

---

## 11. Analytics System

Ambore includes a **built-in, zero-dependency analytics system** — no Google Analytics, no Mixpanel. All data is stored in the project's own PostgreSQL database on Railway.

### How It Works

Every page fires a lightweight event to `POST /api/track`:

```javascript
async function track(event, page) {
  try {
    await fetch(`${API_BASE}/api/track`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ event, page }),
    });
  } catch (_) {}  // never block the user
}

// Usage examples:
track('page_view', 'index');
track('login', 'index');
track('signup', 'index');
track('session_start', 'app');
track('resume_start', 'resume');
```

The backend handler:
```python
@app.post("/api/track", status_code=204)
async def track_event(request: Request, db: Session = Depends(get_db)):
    body = await request.json()
    event = str(body.get("event", ""))[:50]
    page  = str(body.get("page",  ""))[:100]
    if event:
        db.add(PageEvent(event=event, page=page))
        db.commit()
```

### Viewing Analytics

Admin endpoint returns a full breakdown:
```bash
curl -H "x-admin-key: YOUR_ADMIN_KEY" \
  https://web-production-d62ab.up.railway.app/api/admin/analytics
```

Response:
```json
{
  "total_events": 142,
  "today": 18,
  "last_7_days": 89,
  "last_30_days": 142,
  "by_event": {
    "page_view": 80,
    "session_start": 30,
    "login": 20,
    "resume_start": 12
  },
  "by_page": {
    "index": 60,
    "app": 40,
    "jobs": 25,
    "resume": 17
  }
}
```

---

## 12. API Reference

### `GET /api/jobs`

Query parameters:

| Param | Type | Default | Description |
|---|---|---|---|
| `q` | string | — | Full-text search query |
| `category` | string | — | Category filter (e.g. `Cybersecurity`) |
| `state` | string | — | US State filter (e.g. `California`) |
| `work_type` | string | — | `remote` / `hybrid` / `onsite` |
| `experience` | string | — | `entry` / `mid` / `senior` |
| `salary_min` | int | — | Minimum salary in USD |
| `posted_within` | string | — | `1d` / `3d` / `7d` / `14d` / `30d` |
| `source` | string | — | `usajobs` / `adzuna` / `remotive` / `themuse` / `google_jobs` |
| `page` | int | 1 | Page number |
| `per_page` | int | 20 | Results per page (max 100) |
| `sort` | string | `posted_at` | `posted_at` or `salary_max` |

**Example:**
```
GET /api/jobs?q=python&work_type=remote&experience=mid&page=1&per_page=20
```

**Response:**
```json
{
  "jobs": [
    {
      "id": "550e8400-e29b-41d4-a716-446655440000",
      "title": "Python Developer",
      "company": "Acme Corp",
      "location_city": "Austin",
      "location_state": "Texas",
      "work_type": "remote",
      "salary_min": 90000,
      "salary_max": 130000,
      "experience_level": "mid",
      "category": "Software Engineering",
      "skills": ["Python", "FastAPI", "PostgreSQL"],
      "source": "adzuna",
      "posted_at": "2026-02-18T14:00:00Z",
      "apply_url": "https://..."
    }
  ],
  "total": 47,
  "page": 1,
  "per_page": 20,
  "total_pages": 3
}
```

### `GET /api/stats`

Returns portal-wide statistics including total jobs, active jobs, company count, jobs per source, and last scrape time.

### `GET /api/jobs/categories`

Returns all job categories with counts, sorted by count descending.

### `GET /api/jobs/locations`

Returns all US states with job counts, sorted by count descending.

---

## 13. Deployment

### Backend → Railway

Railway is a cloud platform that auto-deploys from a GitHub repository.

**Build configuration (`nixpacks.toml`):**
```toml
[phases.setup]
aptPkgs = ["libpq-dev"]
nixPkgs  = ["python311"]

[phases.build]
cmds = ["pip install -r requirements.txt"]

[start]
cmd = "python -m uvicorn main:app --host 0.0.0.0 --port ${PORT:-8000}"
```

**Process file (`Procfile`):**
```
web: uvicorn main:app --host 0.0.0.0 --port ${PORT:-8000}
```

**Environment variables (set in Railway dashboard):**
```
DATABASE_URL=postgresql://...  # Railway PostgreSQL connection string
ADMIN_KEY=...                  # Secret key for admin endpoints
FRONTEND_URL=https://ambore.org
USAJOBS_API_KEY=...
ADZUNA_APP_ID=...
ADZUNA_API_KEY=...
APIFY_API_TOKEN=...
```

**Database provisioning:**
- Railway PostgreSQL add-on automatically provides `DATABASE_URL`
- `init_db()` runs on startup — creates tables if they don't exist
- No migrations needed (SQLAlchemy `create_all`)

### Frontend → Netlify

Netlify deploys static HTML files directly from GitHub.

**Deploy steps:**
1. Push to `main` branch on `NikhilAmbore/ambore-website`
2. Netlify detects the push and auto-deploys within ~30 seconds
3. No build step — files are served as-is

**Custom domain:**
- `ambore.org` → Netlify DNS
- Auto HTTPS via Let's Encrypt

---

## 14. Live Statistics

As of **2026-02-19**:

| Metric | Value |
|---|---|
| Total active jobs | **1,377** |
| Companies represented | **691** |
| Last scrape | 2026-02-19 07:01 UTC |
| Scrape duration | ~81 seconds |

**Jobs by source:**

| Source | Jobs |
|---|---|
| Adzuna | 1,000 |
| USAJobs | 337 |
| Remotive | 19 |
| Google Jobs (Apify) | 20 |
| The Muse | 1 |

**Jobs by category (top 5):**

| Category | Jobs |
|---|---|
| Other Tech | 575 |
| Cybersecurity | 240 |
| DevOps & Infrastructure | 101 |
| IT Operations & Support | 73 |
| Product & Project Management | 70 |

**Today's scrape (2026-02-19):**

| Source | Added | Skipped (dupes) | Errors |
|---|---|---|---|
| USAJobs | 69 | 134 | 0 |
| Adzuna | 250 | 0 | 0 |
| TheMuse | 0 | 0 | 0 |
| Remotive | 0 | 36 | 0 |
| Google Jobs | 10 | 0 | 0 |
| **Total** | **329** | **170** | **0** |

---

## 15. Project File Structure

```
ambore-website/              ← Frontend (GitHub → Netlify)
├── index.html               # Homepage, auth modal, navigation
├── jobs.html                # Job board with search & filters
├── job-detail.html          # Individual job page
├── resume.html              # AI Resume Builder
└── app.html                 # Interview Co-pilot (AI)

job-portal/
└── backend/                 ← Backend (GitHub → Railway)
    ├── main.py              # FastAPI app, all endpoints
    ├── database.py          # SQLAlchemy engine & session
    ├── models.py            # Job and PageEvent ORM models
    ├── crud.py              # DB queries (get_jobs, upsert, stats)
    ├── schemas.py           # Pydantic request/response models
    ├── scheduler.py         # APScheduler — daily 2AM scrape
    ├── requirements.txt     # Python dependencies
    ├── Procfile             # Railway process definition
    ├── nixpacks.toml        # Railway build config
    └── scrapers/
        ├── base.py          # BaseScraper (categorize, parse, detect)
        ├── usajobs.py       # Federal jobs API
        ├── adzuna.py        # Adzuna job board API
        ├── themuse.py       # The Muse API
        ├── remotive.py      # Remote-only jobs API
        └── apify_google.py  # Google Jobs via Apify Actor
```

---

*Document generated: 2026-02-19 | Platform: Ambore v1.0*
