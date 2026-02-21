#!/usr/bin/env python3
"""
job_scraper.py
==============
Production-ready US job listings extractor.

Supported ATS platforms (via public JSON APIs)
-----------------------------------------------
  Greenhouse      – boards-api.greenhouse.io
  Lever           – api.lever.co
  Workday         – *.myworkdayjobs.com  (public listings endpoint)
  SmartRecruiters – api.smartrecruiters.com
  Ashby           – api.ashbyhq.com
  HTML            – Generic BeautifulSoup scraper (careers page fallback)
  Playwright      – JS-rendered pages (optional, requires playwright install)

Polite scraping
---------------
  • robots.txt respected (cached per domain)
  • Per-domain rate limiting (configurable delay between requests)
  • Exponential-backoff retry on 429 / 5xx
  • Descriptive User-Agent identifying the bot

Output schema (every job normalised to this dict)
-------------------------------------------------
  id              str    SHA-256 fingerprint — stable dedup key
  title           str
  company         str
  location        str    original text from source
  is_remote       bool
  is_usa          bool
  url             str    canonical apply/listing URL
  description     str    plain text, HTML stripped, capped at 4 000 chars
  department      str | None
  employment_type str | None   full_time | part_time | contract | internship
  salary_min      float | None
  salary_max      float | None
  salary_currency str          default "USD"
  posted_at       str | None   ISO-8601
  ats             str          greenhouse | lever | workday | smartrecruiters | ashby | html
  scraped_at      str          ISO-8601 UTC

CLI usage
---------
  python job_scraper.py                              # run built-in example targets → stdout
  python job_scraper.py --config targets.json        # custom targets file
  python job_scraper.py --output jobs.json           # write to file instead of stdout
  python job_scraper.py --verbose                    # debug logging

Programmatic usage
------------------
  from job_scraper import JobScrapeOrchestrator, ScraperTarget

  targets = [
      ScraperTarget(ats="greenhouse", company="stripe"),
      ScraperTarget(ats="lever",      company="figma"),
      ScraperTarget(ats="ashby",      company="linear"),
  ]
  with JobScrapeOrchestrator() as orc:
      jobs = orc.run(targets)          # list[dict]
  print(json.dumps(jobs, indent=2))
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import re
import time
import urllib.robotparser
from abc import ABC, abstractmethod
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from typing import Any
from urllib.parse import urljoin, urlparse

import httpx
from bs4 import BeautifulSoup, Tag

def _safe_json(resp: httpx.Response) -> Any:
    """
    Parse JSON from an httpx response robustly.
    Uses raw bytes so Python's json module handles BOM/encoding detection
    itself, avoiding httpx charset-detection edge-cases under HTTP/2.
    """
    return json.loads(resp.content)

# Optional — only required for JS-heavy pages
try:
    from playwright.sync_api import TimeoutError as PlaywrightTimeout
    from playwright.sync_api import sync_playwright
    PLAYWRIGHT_AVAILABLE = True
except ImportError:
    PLAYWRIGHT_AVAILABLE = False


# ─────────────────────────────────────────────────────────────────────────────
# Logging
# ─────────────────────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("job_scraper")


# ─────────────────────────────────────────────────────────────────────────────
# Constants
# ─────────────────────────────────────────────────────────────────────────────

DEFAULT_HEADERS: dict[str, str] = {
    # Identify the bot clearly — required for ethical scraping.
    "User-Agent": (
        "Mozilla/5.0 (compatible; AmboreJobBot/1.0; +https://ambore.io/bot) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json, text/html, */*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip, deflate, br",
}

REQUEST_TIMEOUT   = 20      # seconds per request
MAX_RETRIES       = 3       # attempts before giving up
RETRY_BACKOFF     = 2.0     # exponential base in seconds  (2^n seconds sleep)
DOMAIN_DELAY      = 1.5     # minimum seconds between requests to same domain
MAX_JOBS_PER_SRC  = 500     # safety cap per source

# ─── US geography ─────────────────────────────────────────────────────────────

US_STATE_ABBREVS: frozenset[str] = frozenset({
    "AL", "AK", "AZ", "AR", "CA", "CO", "CT", "DE", "FL", "GA",
    "HI", "ID", "IL", "IN", "IA", "KS", "KY", "LA", "ME", "MD",
    "MA", "MI", "MN", "MS", "MO", "MT", "NE", "NV", "NH", "NJ",
    "NM", "NY", "NC", "ND", "OH", "OK", "OR", "PA", "RI", "SC",
    "SD", "TN", "TX", "UT", "VT", "VA", "WA", "WV", "WI", "WY",
    # DC + territories
    "DC", "PR", "GU", "VI", "AS", "MP",
})

# Matches explicit US location strings
_RE_US_LOCATION = re.compile(
    r"\b(united\s+states|u\.s\.a?|usa|u\.s\b|america)\b"
    r"|,\s*([A-Z]{2})\b"                                    # ", CA" style
    r"|\bremote[\s\-,]*(us|usa|united\s+states)\b"          # "Remote US"
    r"|\b(us|usa)\s+remote\b",                              # "US Remote"
    re.IGNORECASE,
)

_RE_REMOTE = re.compile(
    r"\b(remote|work[\s\-]+from[\s\-]+home|wfh|distributed|anywhere)\b",
    re.IGNORECASE,
)

# Normalise employment type strings to a canonical set
_EMPLOYMENT_TYPE_MAP: dict[str, str] = {
    "full time":    "full_time",
    "full-time":    "full_time",
    "fulltime":     "full_time",
    "full_time":    "full_time",
    "part time":    "part_time",
    "part-time":    "part_time",
    "parttime":     "part_time",
    "part_time":    "part_time",
    "contract":     "contract",
    "contractor":   "contract",
    "freelance":    "contract",
    "internship":   "internship",
    "intern":       "internship",
    "temporary":    "temporary",
    "temp":         "temporary",
}


# ─────────────────────────────────────────────────────────────────────────────
# Job schema
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class Job:
    """Normalised job posting.  All scrapers produce instances of this class."""

    id:               str
    title:            str
    company:          str
    location:         str
    is_remote:        bool
    is_usa:           bool
    url:              str
    description:      str
    department:       str | None      = None
    employment_type:  str | None      = None
    salary_min:       float | None    = None
    salary_max:       float | None    = None
    salary_currency:  str             = "USD"
    posted_at:        str | None      = None
    ats:              str             = ""
    scraped_at:       str             = field(
        default_factory=lambda: datetime.now(timezone.utc).isoformat()
    )

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


# ─────────────────────────────────────────────────────────────────────────────
# Pure utility functions
# ─────────────────────────────────────────────────────────────────────────────

def _make_id(title: str, company: str, location: str) -> str:
    """16-char hex fingerprint used as a stable deduplication key."""
    raw = f"{title.lower().strip()}|{company.lower().strip()}|{location.lower().strip()}"
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


def _strip_html(html: str) -> str:
    """Convert HTML markup to plain text, collapsing whitespace."""
    if not html:
        return ""
    soup = BeautifulSoup(html, "html.parser")
    text = soup.get_text(" ", strip=True)
    return re.sub(r"\s{2,}", " ", text)


def _classify_location(location: str) -> tuple[bool, bool]:
    """
    Return ``(is_usa, is_remote)``.

    Conservative — only returns ``is_usa=True`` when a clear US indicator is
    present.  A bare "Remote" without a country context returns
    ``(False, True)``; callers apply ``assume_us_remote`` heuristic separately.
    """
    if not location:
        return False, False

    is_remote = bool(_RE_REMOTE.search(location))
    m = _RE_US_LOCATION.search(location)
    if m:
        # Group 2 captures a 2-letter state abbreviation; validate it.
        state = m.group(2)
        if state and state.upper() not in US_STATE_ABBREVS:
            return False, is_remote
        return True, is_remote

    return False, is_remote


def _parse_salary(text: str) -> tuple[float | None, float | None, str]:
    """
    Extract ``(min, max, currency)`` from a free-form salary string.

    Handles:  "$120k – $180k",  "120,000 - 200,000 USD",  "£50,000"
    """
    if not text:
        return None, None, "USD"

    currency = "USD"
    tl = text.lower()
    if "£" in text or "gbp" in tl:
        currency = "GBP"
    elif "€" in text or "eur" in tl:
        currency = "EUR"
    elif "cad" in tl or "c$" in tl:
        currency = "CAD"

    # Find all numeric values; check if immediately followed by 'k'
    values: list[float] = []
    for m in re.finditer(r"([\d,]+(?:\.\d+)?)\s*([kK])?", text):
        raw_num, k_suffix = m.group(1), m.group(2)
        try:
            v = float(raw_num.replace(",", ""))
            if k_suffix:
                v *= 1_000
            values.append(v)
        except ValueError:
            continue

    if len(values) >= 2:
        return min(values), max(values), currency
    if len(values) == 1:
        return values[0], None, currency
    return None, None, currency


def _normalise_employment_type(raw: str | None) -> str | None:
    if not raw:
        return None
    return _EMPLOYMENT_TYPE_MAP.get(raw.lower().strip(), raw.lower().strip() or None)


# ─────────────────────────────────────────────────────────────────────────────
# PoliteClient — rate-limited, robots.txt-aware httpx wrapper
# ─────────────────────────────────────────────────────────────────────────────

class PoliteClient:
    """
    Thin wrapper around ``httpx.Client`` that adds:

    * **robots.txt respect** — fetches and caches ``/robots.txt`` per domain,
      raises ``PermissionError`` if the URL is disallowed.
    * **Rate limiting** — enforces ``domain_delay`` seconds between successive
      requests to the same domain.
    * **Retry with exponential backoff** — retries on HTTP 429, 5xx, and
      network/timeout errors up to ``max_retries`` times.
    """

    def __init__(
        self,
        headers:      dict[str, str] | None = None,
        timeout:      float = REQUEST_TIMEOUT,
        domain_delay: float = DOMAIN_DELAY,
        max_retries:  int   = MAX_RETRIES,
    ) -> None:
        self._headers      = {**DEFAULT_HEADERS, **(headers or {})}
        self._timeout      = timeout
        self._domain_delay = domain_delay
        self._max_retries  = max_retries

        # State per domain
        self._last_req: dict[str, float]                          = {}
        self._robots:   dict[str, urllib.robotparser.RobotFileParser | None] = {}

        self._client = httpx.Client(
            headers=self._headers,
            timeout=self._timeout,
            follow_redirects=True,
            http2=True,
        )

    # ── robots.txt ────────────────────────────────────────────────────────────

    def _get_robots(self, domain: str) -> urllib.robotparser.RobotFileParser | None:
        if domain not in self._robots:
            rp = urllib.robotparser.RobotFileParser()
            rp.set_url(f"{domain}/robots.txt")
            try:
                rp.read()
                self._robots[domain] = rp
            except Exception:
                # Unable to fetch robots.txt — assume allowed (fail-open)
                log.debug("Could not read robots.txt for %s — proceeding", domain)
                self._robots[domain] = None
        return self._robots[domain]

    def _robots_allow(self, url: str) -> bool:
        parsed = urlparse(url)
        domain = f"{parsed.scheme}://{parsed.netloc}"
        rp = self._get_robots(domain)
        if rp is None:
            return True
        return rp.can_fetch(self._headers["User-Agent"], url)

    # ── Rate limiting ─────────────────────────────────────────────────────────

    def _rate_limit(self, url: str) -> None:
        domain  = urlparse(url).netloc
        elapsed = time.monotonic() - self._last_req.get(domain, 0.0)
        wait    = self._domain_delay - elapsed
        if wait > 0:
            time.sleep(wait)
        self._last_req[domain] = time.monotonic()

    # ── Public interface ──────────────────────────────────────────────────────

    def get(self, url: str, **kwargs: Any) -> httpx.Response:
        return self._request("GET", url, **kwargs)

    def post(self, url: str, **kwargs: Any) -> httpx.Response:
        return self._request("POST", url, **kwargs)

    def _request(self, method: str, url: str, **kwargs: Any) -> httpx.Response:
        if not self._robots_allow(url):
            raise PermissionError(f"robots.txt disallows fetching: {url}")

        for attempt in range(1, self._max_retries + 1):
            self._rate_limit(url)
            try:
                resp = self._client.request(method, url, **kwargs)

                if resp.status_code == 429:
                    wait = int(resp.headers.get("Retry-After", RETRY_BACKOFF ** attempt))
                    log.warning("Rate-limited by %s — waiting %ds (attempt %d)", url, wait, attempt)
                    time.sleep(wait)
                    continue

                if resp.status_code >= 500:
                    wait = RETRY_BACKOFF ** attempt
                    log.warning("Server error %d from %s — retrying in %.1fs (attempt %d/%d)",
                                resp.status_code, url, wait, attempt, self._max_retries)
                    time.sleep(wait)
                    continue

                resp.raise_for_status()
                return resp

            except (httpx.TimeoutException, httpx.NetworkError) as exc:
                if attempt == self._max_retries:
                    raise
                wait = RETRY_BACKOFF ** attempt
                log.warning("%s on %s — retrying in %.1fs (%d/%d)", exc, url, wait, attempt, self._max_retries)
                time.sleep(wait)

        raise RuntimeError(f"All {self._max_retries} attempts exhausted for {method} {url}")

    # ── Context manager ───────────────────────────────────────────────────────

    def close(self) -> None:
        self._client.close()

    def __enter__(self) -> "PoliteClient":
        return self

    def __exit__(self, *_: Any) -> None:
        self.close()


# ─────────────────────────────────────────────────────────────────────────────
# Target configuration
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class ScraperTarget:
    """
    One scrape target.  Required fields depend on ``ats`` type.

    Common fields
    -------------
    ats           "greenhouse" | "lever" | "workday" | "smartrecruiters"
                  | "ashby" | "html" | "playwright"
    company       ATS-specific slug (e.g. "stripe", "airbnb")
    company_name  Human-readable display name (auto-derived from ``company``)

    Workday-specific
    ----------------
    wd_tenant     Workday tenant subdomain  (e.g. "stripe")
    wd_site       Careers site name        (e.g. "Stripe")
    wd_instance   Workday instance number  (default "wd5")

    HTML/Playwright-specific
    ------------------------
    careers_url   Direct URL to the careers / jobs listing page

    Behaviour flags
    ---------------
    assume_us_remote
        If True (default), treat listings whose location is only "Remote"
        (with no country) as US Remote — appropriate for US-focused companies.
    """

    ats:              str
    company:          str
    company_name:     str  = ""
    # Workday
    wd_tenant:        str  = ""
    wd_site:          str  = ""
    wd_instance:      str  = "wd5"
    # HTML / Playwright
    careers_url:      str  = ""
    # API credentials (USAJobs, future paid APIs)
    api_key:          str  = ""
    user_email:       str  = ""
    # Behaviour
    assume_us_remote: bool = True

    def __post_init__(self) -> None:
        if not self.company_name:
            self.company_name = self.company.replace("-", " ").replace("_", " ").title()


# ─────────────────────────────────────────────────────────────────────────────
# Abstract base scraper
# ─────────────────────────────────────────────────────────────────────────────

class BaseScraper(ABC):
    """
    All ATS-specific scrapers inherit from this.

    Subclasses implement ``fetch_jobs()`` and call ``self._make_job(...)``
    to produce normalised ``Job`` objects.  ``_make_job`` returns ``None``
    for non-US listings so callers can filter with a simple list comprehension.
    """

    ATS_NAME: str = "unknown"

    def __init__(self, client: PoliteClient, target: ScraperTarget) -> None:
        self.client = client
        self.target = target

    @abstractmethod
    def fetch_jobs(self) -> list[Job]:
        ...

    def _make_job(
        self,
        title:            str,
        location:         str,
        url:              str,
        description:      str        = "",
        department:       str | None = None,
        employment_type:  str | None = None,
        salary_text:      str | None = None,
        posted_at:        str | None = None,
        company_override: str | None = None,   # aggregators pass real company name
    ) -> Job | None:
        """
        Normalise raw fields and return a ``Job``, or ``None`` if the listing
        is not in the USA (after applying the ``assume_us_remote`` heuristic).
        ``company_override`` lets aggregator scrapers (The Muse, Remotive, USAJobs)
        pass the real hiring-company name without changing ``target.company_name``.
        """
        title    = (title or "").strip()
        location = (location or "").strip()
        company  = company_override or self.target.company_name

        if not title:
            return None

        is_usa, is_remote = _classify_location(location)

        # Heuristic: bare "Remote" with no country → treat as US Remote
        if not is_usa and is_remote and self.target.assume_us_remote:
            is_usa = True

        if not is_usa:
            return None

        sal_min, sal_max, sal_curr = _parse_salary(salary_text or "")

        return Job(
            id=_make_id(title, company, location),
            title=title,
            company=company,
            location=location,
            is_remote=is_remote,
            is_usa=True,
            url=url,
            description=_strip_html(description)[:4_000],
            department=department,
            employment_type=_normalise_employment_type(employment_type),
            salary_min=sal_min,
            salary_max=sal_max,
            salary_currency=sal_curr,
            posted_at=posted_at,
            ats=self.ATS_NAME,
        )


# ─────────────────────────────────────────────────────────────────────────────
# Greenhouse
# ─────────────────────────────────────────────────────────────────────────────

class GreenhouseScraper(BaseScraper):
    """
    Greenhouse public JSON API — no authentication required.

    API reference: https://developers.greenhouse.io/job-board.html
    Endpoint: GET https://boards-api.greenhouse.io/v1/boards/{company}/jobs?content=true
    """

    ATS_NAME = "greenhouse"
    _API_URL = "https://boards-api.greenhouse.io/v1/boards/{company}/jobs"
    _JOB_URL = "https://boards.greenhouse.io/{company}/jobs/{job_id}"

    def fetch_jobs(self) -> list[Job]:
        company = self.target.company
        url = self._API_URL.format(company=company)
        log.info("[Greenhouse] %s — fetching job list", company)

        try:
            resp = self.client.get(url, params={"content": "true"})
            data = _safe_json(resp)
        except Exception as exc:
            log.error("[Greenhouse] %s — %s", company, exc)
            return []

        jobs: list[Job] = []
        for raw in data.get("jobs", []):
            # Location: prefer office names → fall back to location object
            offices   = raw.get("offices", [])
            location  = (
                ", ".join(o.get("name", "") for o in offices if o.get("name"))
                or raw.get("location", {}).get("name", "")
            )

            dept_list  = raw.get("departments", [])
            department = dept_list[0].get("name") if dept_list else None

            job = self._make_job(
                title=raw.get("title", ""),
                location=location,
                url=(
                    raw.get("absolute_url")
                    or self._JOB_URL.format(company=company, job_id=raw.get("id", ""))
                ),
                description=raw.get("content", ""),
                department=department,
                posted_at=raw.get("updated_at"),
            )
            if job:
                jobs.append(job)

        log.info("[Greenhouse] %s — %d US jobs", company, len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# Lever
# ─────────────────────────────────────────────────────────────────────────────

class LeverScraper(BaseScraper):
    """
    Lever public postings API — no authentication required.

    API reference: https://help.lever.co/hc/en-us/articles/206390065
    Endpoint: GET https://api.lever.co/v0/postings/{company}?mode=json
    """

    ATS_NAME = "lever"
    _API_URL = "https://api.lever.co/v0/postings/{company}"
    _JOB_URL = "https://jobs.lever.co/{company}/{job_id}"

    def fetch_jobs(self) -> list[Job]:
        company = self.target.company
        url = self._API_URL.format(company=company)
        log.info("[Lever] %s — fetching job list", company)

        try:
            resp = self.client.get(url, params={"mode": "json", "limit": 500})
            data = _safe_json(resp)
        except Exception as exc:
            log.error("[Lever] %s — %s", company, exc)
            return []

        jobs: list[Job] = []
        for raw in (data if isinstance(data, list) else []):
            cats = raw.get("categories", {})

            location   = cats.get("location", "") or raw.get("workplaceType", "")
            commitment = cats.get("commitment", "")
            department = cats.get("department") or cats.get("team")

            # Salary range (available in some job boards)
            sal_text = ""
            sr = raw.get("salaryRange") or {}
            if sr:
                lo   = sr.get("min", "")
                hi   = sr.get("max", "")
                curr = sr.get("currency", "USD")
                if lo or hi:
                    sal_text = f"{lo}-{hi} {curr}"

            # Compose description from all text sections
            description = "\n\n".join(filter(None, [
                raw.get("descriptionPlain", ""),
                *(ls.get("content", "") for ls in raw.get("lists", [])),
                raw.get("additionalPlain", ""),
            ]))

            created_ms = raw.get("createdAt")
            posted_at  = (
                datetime.fromtimestamp(created_ms / 1_000, tz=timezone.utc).isoformat()
                if created_ms else None
            )

            job = self._make_job(
                title=raw.get("text", ""),
                location=location,
                url=(
                    raw.get("hostedUrl")
                    or self._JOB_URL.format(company=company, job_id=raw.get("id", ""))
                ),
                description=description,
                department=department,
                employment_type=commitment,
                salary_text=sal_text,
                posted_at=posted_at,
            )
            if job:
                jobs.append(job)

        log.info("[Lever] %s — %d US jobs", company, len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# SmartRecruiters
# ─────────────────────────────────────────────────────────────────────────────

class SmartRecruitersScraper(BaseScraper):
    """
    SmartRecruiters public postings API — no authentication required.

    API reference: https://developers.smartrecruiters.com/docs/public-api-overview
    Endpoint: GET https://api.smartrecruiters.com/v1/companies/{company}/postings
    """

    ATS_NAME = "smartrecruiters"
    _API_URL = "https://api.smartrecruiters.com/v1/companies/{company}/postings"

    def fetch_jobs(self) -> list[Job]:
        company = self.target.company
        url = self._API_URL.format(company=company)
        log.info("[SmartRecruiters] %s — fetching job list", company)

        jobs:   list[Job] = []
        offset  = 0
        limit   = 100

        while len(jobs) < MAX_JOBS_PER_SRC:
            try:
                resp = self.client.get(url, params={"limit": limit, "offset": offset})
                data = _safe_json(resp)
            except Exception as exc:
                log.error("[SmartRecruiters] %s — %s", company, exc)
                break

            postings = data.get("content", [])
            if not postings:
                break

            for raw in postings:
                loc      = raw.get("location") or {}
                country  = (loc.get("country") or "").upper()

                # Skip postings explicitly tagged to non-US countries
                if country and country not in {"US", "USA", ""}:
                    continue

                city   = loc.get("city", "")
                region = loc.get("region", "")
                loc_parts = [p for p in (city, region, country) if p and p not in {"US", "USA"}]
                location  = ", ".join(loc_parts) if loc_parts else "United States"

                # SmartRecruiters remote flag
                is_wfh = loc.get("remote") or raw.get("workFromHome") == "true"
                if is_wfh and not city:
                    location = "Remote, US"

                dept     = (raw.get("department") or {}).get("label")
                emp_type = (raw.get("typeOfEmployment") or {}).get("label")
                posted   = raw.get("releasedDate")
                job_url  = raw.get("ref") or (
                    f"https://careers.smartrecruiters.com/{company}/{raw.get('id', '')}"
                )

                job = self._make_job(
                    title=raw.get("name", ""),
                    location=location,
                    url=job_url,
                    department=dept,
                    employment_type=emp_type,
                    posted_at=posted,
                )
                if job:
                    jobs.append(job)

            total  = data.get("totalFound", 0)
            offset += limit
            if offset >= total:
                break

        log.info("[SmartRecruiters] %s — %d US jobs", company, len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# Ashby
# ─────────────────────────────────────────────────────────────────────────────

class AshbyScraper(BaseScraper):
    """
    Ashby public job-board API — no authentication required.

    API reference: https://developers.ashbyhq.com/docs/job-board-api
    Endpoint: GET https://api.ashbyhq.com/posting-api/job-board/{company}
    """

    ATS_NAME = "ashby"
    _API_URL = "https://api.ashbyhq.com/posting-api/job-board/{company}"
    _JOB_URL = "https://jobs.ashbyhq.com/{company}/{job_id}"

    def fetch_jobs(self) -> list[Job]:
        company = self.target.company
        url = self._API_URL.format(company=company)
        log.info("[Ashby] %s — fetching job list", company)

        try:
            resp = self.client.get(url, params={"includeCompensation": "1"})
            data = _safe_json(resp)
        except Exception as exc:
            log.error("[Ashby] %s — %s", company, exc)
            return []

        # Build a location-id → name map from the board metadata
        location_map: dict[str, str] = {
            loc["id"]: loc.get("name", "")
            for loc in data.get("locationIds", [])
            if isinstance(loc, dict) and "id" in loc
        }

        jobs: list[Job] = []
        for raw in data.get("jobs", []):
            # Prefer resolved location names; fall back to the flat location field
            loc_ids  = raw.get("locationIds") or []
            loc_names = [location_map.get(lid, "") for lid in loc_ids if location_map.get(lid)]
            location  = "; ".join(loc_names) if loc_names else raw.get("location", "")

            if raw.get("isRemote") and not location:
                location = "Remote, US"

            # Compensation
            sal_text = ""
            comp = raw.get("compensation") or {}
            if comp:
                lo   = comp.get("minValue", "")
                hi   = comp.get("maxValue", "")
                curr = comp.get("currency", "USD")
                interval = comp.get("interval", "")
                if lo or hi:
                    sal_text = f"{lo}-{hi} {curr}/{interval}"

            posted_at = raw.get("publishedAt") or raw.get("updatedAt")

            job = self._make_job(
                title=raw.get("title", ""),
                location=location,
                url=(
                    raw.get("jobUrl")
                    or self._JOB_URL.format(company=company, job_id=raw.get("id", ""))
                ),
                description=raw.get("descriptionHtml") or raw.get("description", ""),
                department=raw.get("department") or raw.get("teamName"),
                employment_type=raw.get("employmentType"),
                salary_text=sal_text,
                posted_at=posted_at,
            )
            if job:
                jobs.append(job)

        log.info("[Ashby] %s — %d US jobs", company, len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# Workday (public listings API)
# ─────────────────────────────────────────────────────────────────────────────

class WorkdayScraper(BaseScraper):
    """
    Workday public jobs API — no authentication required (public listings).

    Requires ``target.wd_tenant``, ``target.wd_site``, and optionally
    ``target.wd_instance`` (default "wd5").

    Example — Microsoft:
        wd_tenant="microsoftcorporation"
        wd_site="External_Microsoft_Careers_Portal"
        wd_instance="wd1"
    → https://microsoftcorporation.wd1.myworkdayjobs.com/wday/cxs/
          microsoftcorporation/External_Microsoft_Careers_Portal/jobs

    The API paginates in pages of 20.  Location is filtered post-fetch because
    Workday does not expose a query-time country filter on the public endpoint.
    """

    ATS_NAME = "workday"
    _API_TPL = (
        "https://{tenant}.{instance}.myworkdayjobs.com"
        "/wday/cxs/{tenant}/{site}/jobs"
    )
    _JOB_TPL = "https://{tenant}.{instance}.myworkdayjobs.com{path}"

    def fetch_jobs(self) -> list[Job]:
        t = self.target
        if not t.wd_tenant or not t.wd_site:
            log.error("[Workday] wd_tenant and wd_site are required for %s", t.company)
            return []

        tenant   = t.wd_tenant
        site     = t.wd_site
        instance = t.wd_instance or "wd5"
        api_url  = self._API_TPL.format(tenant=tenant, site=site, instance=instance)

        log.info("[Workday] %s — fetching job list", tenant)

        jobs:   list[Job] = []
        offset  = 0
        limit   = 20          # Workday default page size

        while len(jobs) < MAX_JOBS_PER_SRC:
            payload = {
                "appliedFacets": {},
                "limit": limit,
                "offset": offset,
                "searchText": "",
            }
            try:
                resp = self.client.post(
                    api_url,
                    json=payload,
                    headers={"Content-Type": "application/json"},
                )
                data = _safe_json(resp)
            except Exception as exc:
                log.error("[Workday] %s — %s", tenant, exc)
                break

            postings = data.get("jobPostings", [])
            if not postings:
                break

            for raw in postings:
                ext_path  = raw.get("externalPath", "")
                job_url   = self._JOB_TPL.format(tenant=tenant, instance=instance, path=ext_path)
                location  = raw.get("locationsText", "")

                # Workday may expose a remoteType string ("Fully Remote", etc.)
                remote_type = raw.get("remoteType", "")
                if remote_type:
                    location = f"{remote_type} — {location}".strip(" —")

                time_type = raw.get("timeType", "")  # "Full time" | "Part time"
                posted_on = raw.get("postedOn")       # e.g. "Posted 3 Days Ago" — string

                job = self._make_job(
                    title=raw.get("title", ""),
                    location=location,
                    url=job_url,
                    employment_type=time_type,
                    posted_at=posted_on,
                )
                if job:
                    jobs.append(job)

            total   = data.get("total", 0)
            offset += limit
            if offset >= total:
                break

        log.info("[Workday] %s — %d US jobs", tenant, len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# Generic HTML scraper (BeautifulSoup)
# ─────────────────────────────────────────────────────────────────────────────

class GenericHTMLScraper(BaseScraper):
    """
    Heuristic BeautifulSoup scraper for company career pages that don't use
    a known ATS.  Tries a prioritised list of CSS selectors to find job cards,
    then extracts title, location, and link from each card.

    Set ``target.careers_url`` to the page to scrape.

    Note: If the page requires JavaScript rendering, use ``PlaywrightScraper``
    instead.
    """

    ATS_NAME = "html"

    # Tried in order — first selector that returns elements wins
    _JOB_SELECTORS: list[str] = [
        "[class*='job-item']", "[class*='job-card']", "[class*='job-listing']",
        "[class*='posting-item']", "[class*='opening-row']",
        "li[class*='job']", "li[class*='position']", "li[class*='opening']",
        "div[class*='job']", "article[class*='job']",
        ".position", ".opening", ".career-item",
    ]
    _TITLE_SELECTORS:    list[str] = [
        "h1", "h2", "h3", "h4",
        "[class*='title']", "[class*='name']", "[class*='position']", "a",
    ]
    _LOCATION_SELECTORS: list[str] = [
        "[class*='location']", "[class*='city']", "[class*='region']",
        "[class*='office']", "[class*='place']", "[class*='meta']",
    ]

    def fetch_jobs(self) -> list[Job]:
        url = self.target.careers_url
        if not url:
            log.error("[HTML] careers_url is required for %s", self.target.company)
            return []

        log.info("[HTML] %s — fetching %s", self.target.company_name, url)
        try:
            resp = self.client.get(url)
            html = resp.text
        except Exception as exc:
            log.error("[HTML] %s — %s", url, exc)
            return []

        soup        = BeautifulSoup(html, "html.parser")
        job_els     = self._find_job_elements(soup)

        if not job_els:
            log.warning("[HTML] No job elements found on %s — page may require JavaScript", url)
            return []

        parsed    = urlparse(url)
        base_url  = f"{parsed.scheme}://{parsed.netloc}"
        jobs: list[Job] = []

        for el in job_els[:MAX_JOBS_PER_SRC]:
            title    = self._first_text(el, self._TITLE_SELECTORS)
            location = self._first_text(el, self._LOCATION_SELECTORS)

            link_tag = el.find("a", href=True) if el.name != "a" else el
            job_url  = urljoin(base_url, link_tag["href"]) if link_tag else url

            if not title:
                continue

            job = self._make_job(
                title=title,
                location=location or "United States",
                url=job_url,
            )
            if job:
                jobs.append(job)

        log.info("[HTML] %s — %d US jobs", self.target.company_name, len(jobs))
        return jobs

    def _find_job_elements(self, soup: BeautifulSoup) -> list[Tag]:
        for sel in self._JOB_SELECTORS:
            elements = soup.select(sel)
            if elements:
                return elements
        return []

    @staticmethod
    def _first_text(el: Tag, selectors: list[str]) -> str:
        for sel in selectors:
            found = el.select_one(sel)
            if found:
                text = found.get_text(strip=True)
                if text:
                    return text
        return ""


# ─────────────────────────────────────────────────────────────────────────────
# Playwright scraper — JS-rendered pages
# ─────────────────────────────────────────────────────────────────────────────

class PlaywrightScraper(BaseScraper):
    """
    Uses a headless Chromium browser (via Playwright) to render pages that
    require JavaScript before BeautifulSoup can parse them.

    Install:
        pip install playwright
        playwright install chromium

    Set ``target.careers_url`` to the page to render.
    """

    ATS_NAME = "playwright_html"

    def fetch_jobs(self) -> list[Job]:
        if not PLAYWRIGHT_AVAILABLE:
            log.error(
                "[Playwright] Not installed.  Run: pip install playwright && playwright install chromium"
            )
            return []

        url = self.target.careers_url
        if not url:
            log.error("[Playwright] careers_url is required for %s", self.target.company)
            return []

        log.info("[Playwright] %s — rendering %s", self.target.company_name, url)
        html = self._render_page(url)
        if not html:
            return []

        # Delegate HTML parsing to GenericHTMLScraper logic
        delegate  = GenericHTMLScraper(self.client, self.target)
        soup      = BeautifulSoup(html, "html.parser")
        job_els   = delegate._find_job_elements(soup)

        parsed   = urlparse(url)
        base_url = f"{parsed.scheme}://{parsed.netloc}"
        jobs: list[Job] = []

        for el in job_els[:MAX_JOBS_PER_SRC]:
            title    = delegate._first_text(el, GenericHTMLScraper._TITLE_SELECTORS)
            location = delegate._first_text(el, GenericHTMLScraper._LOCATION_SELECTORS)
            link_tag = el.find("a", href=True) if el.name != "a" else el
            job_url  = urljoin(base_url, link_tag["href"]) if link_tag else url

            if not title:
                continue

            job = self._make_job(
                title=title,
                location=location or "United States",
                url=job_url,
            )
            if job:
                jobs.append(job)

        log.info("[Playwright] %s — %d US jobs", self.target.company_name, len(jobs))
        return jobs

    @staticmethod
    def _render_page(url: str, wait_ms: int = 3_000) -> str:
        """Launch headless Chromium, wait for network idle, return full HTML."""
        try:
            with sync_playwright() as pw:
                browser = pw.chromium.launch(headless=True)
                context = browser.new_context(
                    user_agent=DEFAULT_HEADERS["User-Agent"],
                    extra_http_headers={"Accept-Language": "en-US,en;q=0.9"},
                )
                page = context.new_page()
                page.goto(url, wait_until="networkidle", timeout=30_000)
                page.wait_for_timeout(wait_ms)
                html = page.content()
                browser.close()
                return html
        except PlaywrightTimeout:
            log.error("[Playwright] Timeout rendering %s", url)
            return ""
        except Exception as exc:
            log.error("[Playwright] %s", exc)
            return ""


# ─────────────────────────────────────────────────────────────────────────────
# The Muse  (API/Feed Integration — free, no auth)
# ─────────────────────────────────────────────────────────────────────────────

class TheMuseScraper(BaseScraper):
    """
    The Muse public jobs API — no authentication required.

    Docs: https://www.themuse.com/developers/api/v2
    Endpoint: GET https://www.themuse.com/api/public/jobs
    Fetches US tech jobs across 7 categories, up to 5 pages each.
    """

    ATS_NAME = "themuse"
    _API_URL  = "https://www.themuse.com/api/public/jobs"
    _TECH_CATEGORIES = [
        "Engineering", "Data Science", "IT", "Product",
        "Design", "Computer Science", "User Experience",
    ]

    def fetch_jobs(self) -> list[Job]:
        log.info("[TheMuse] Fetching US tech jobs")
        jobs:     list[Job] = []
        seen_ids: set[str]  = set()

        for category in self._TECH_CATEGORIES:
            if len(jobs) >= MAX_JOBS_PER_SRC:
                break
            for page in range(10):          # max 10 pages × 20 = 200 per category
                if len(jobs) >= MAX_JOBS_PER_SRC:
                    break
                try:
                    resp = self.client.get(self._API_URL, params={
                        "category": category,
                        "page": page,
                        "per_page": 20,
                    })
                    data = _safe_json(resp)
                except Exception as exc:
                    log.error("[TheMuse] %s p%d — %s", category, page, exc)
                    break

                results = data.get("results", [])
                if not results:
                    break

                for raw in results:
                    job_id = str(raw.get("id", ""))
                    if job_id in seen_ids:
                        continue
                    seen_ids.add(job_id)

                    locs     = raw.get("locations", [])
                    location = "; ".join(l.get("name", "") for l in locs if l.get("name")) or ""

                    levels   = raw.get("levels", [])
                    emp_type = levels[0].get("name") if levels else None

                    cats = raw.get("categories", [])
                    dept = cats[0].get("name") if cats else category

                    company_name = (raw.get("company") or {}).get("name", "")
                    job_url      = (raw.get("refs") or {}).get("landing_page", "")
                    posted_at    = raw.get("publication_date")

                    job = self._make_job(
                        title=raw.get("name", ""),
                        location=location,
                        url=job_url,
                        description=raw.get("contents", ""),
                        department=dept,
                        employment_type=emp_type,
                        posted_at=posted_at,
                        company_override=company_name or "The Muse",
                    )
                    if job:
                        jobs.append(job)

                # Stop if this was the last page
                if len(results) < 20:
                    break

            log.info("[TheMuse] %s — %d US jobs so far", category, len(jobs))

        log.info("[TheMuse] Total: %d US jobs", len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# Remotive  (API/Feed Integration — free, no auth, remote-only)
# ─────────────────────────────────────────────────────────────────────────────

class RemotiveScraper(BaseScraper):
    """
    Remotive public remote-jobs API — no authentication required.

    Docs: https://remotive.com/api
    Endpoint: GET https://remotive.com/api/remote-jobs
    All Remotive jobs are remote; we include ones with US-allowed locations.
    """

    ATS_NAME = "remotive"
    _API_URL  = "https://remotive.com/api/remote-jobs"
    _TECH_CATEGORIES = [
        "software-dev", "devops", "data", "product", "design",
        "qa", "backend", "frontend", "mobile", "engineering",
    ]

    # Candidate-location strings that indicate US-allowed roles
    _US_HINTS = re.compile(
        r"\b(usa|united\s+states|u\.s|north\s+america|americas|worldwide|anywhere)\b",
        re.IGNORECASE,
    )

    def fetch_jobs(self) -> list[Job]:
        log.info("[Remotive] Fetching remote US-eligible tech jobs")
        jobs:     list[Job] = []
        seen_ids: set[str]  = set()

        for category in self._TECH_CATEGORIES:
            if len(jobs) >= MAX_JOBS_PER_SRC:
                break
            try:
                resp = self.client.get(self._API_URL, params={
                    "category": category,
                    "limit": 100,
                })
                data = _safe_json(resp)
            except Exception as exc:
                log.error("[Remotive] %s — %s", category, exc)
                continue

            for raw in data.get("jobs", []):
                job_id = str(raw.get("id", ""))
                if job_id in seen_ids:
                    continue
                seen_ids.add(job_id)

                # Filter: only jobs open to US candidates
                candidate_loc = raw.get("candidate_required_location", "")
                if candidate_loc and not self._US_HINTS.search(candidate_loc):
                    continue

                location  = f"Remote — {candidate_loc}" if candidate_loc else "Remote, US"
                posted_at = raw.get("publication_date")

                job = self._make_job(
                    title=raw.get("title", ""),
                    location=location,
                    url=raw.get("url", ""),
                    description=raw.get("description", ""),
                    department=raw.get("category", category),
                    employment_type=raw.get("job_type"),
                    salary_text=raw.get("salary", ""),
                    posted_at=posted_at,
                    company_override=raw.get("company_name", ""),
                )
                if job:
                    jobs.append(job)

            log.info("[Remotive] %s — %d US jobs so far", category, len(jobs))

        log.info("[Remotive] Total: %d US jobs", len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# USAJobs  (API/Feed Integration — free with API key, government postings)
# ─────────────────────────────────────────────────────────────────────────────

class USAJobsScraper(BaseScraper):
    """
    USAJobs.gov official REST API — free, requires registration.

    Register at: https://developer.usajobs.gov/
    Requires ``target.api_key`` and ``target.user_email``.

    Docs: https://developer.usajobs.gov/APIs/Search
    Endpoint: GET https://data.usajobs.gov/api/search
    Fetches US federal government tech job postings.
    """

    ATS_NAME = "usajobs"
    _API_URL  = "https://data.usajobs.gov/api/search"
    _KEYWORDS = [
        "software engineer", "data scientist", "cybersecurity",
        "cloud engineer", "devops", "IT specialist", "systems administrator",
        "machine learning", "python developer", "network engineer",
    ]

    def fetch_jobs(self) -> list[Job]:
        api_key = self.target.api_key
        email   = self.target.user_email
        if not api_key or not email:
            log.warning("[USAJobs] api_key and user_email are required — skipping")
            return []

        log.info("[USAJobs] Fetching government tech jobs")
        jobs:     list[Job] = []
        seen_ids: set[str]  = set()
        auth_headers = {
            "Authorization-Key": api_key,
            "User-Agent":        email,
            "Host":              "data.usajobs.gov",
        }

        for keyword in self._KEYWORDS:
            if len(jobs) >= MAX_JOBS_PER_SRC:
                break
            page = 1
            while len(jobs) < MAX_JOBS_PER_SRC:
                try:
                    resp = self.client.get(
                        self._API_URL,
                        params={
                            "Keyword":        keyword,
                            "ResultsPerPage": 25,
                            "Page":           page,
                            "WhoMayApply":    "public",
                        },
                        headers=auth_headers,
                    )
                    data = _safe_json(resp)
                except Exception as exc:
                    log.error("[USAJobs] %s p%d — %s", keyword, page, exc)
                    break

                results = (
                    data.get("SearchResult", {})
                        .get("SearchResultItems", [])
                )
                if not results:
                    break

                for raw in results:
                    mv = raw.get("MatchedObjectDescriptor", {})
                    job_id = mv.get("PositionID", "")
                    if job_id in seen_ids:
                        continue
                    seen_ids.add(job_id)

                    locs = mv.get("PositionLocation", [])
                    location = "; ".join(
                        f"{l.get('CityName', '')}, {l.get('CountrySubDivisionCode', '')}".strip(", ")
                        for l in locs
                    ) or "United States"

                    pay = mv.get("PositionRemuneration", [{}])[0]
                    sal_min = float(pay.get("MinimumRange", 0) or 0) or None
                    sal_max = float(pay.get("MaximumRange", 0) or 0) or None
                    sal_txt = f"{sal_min}-{sal_max}" if sal_min else ""

                    start_date = mv.get("PublicationStartDate", "")
                    end_date   = mv.get("ApplicationCloseDate", "")

                    job = self._make_job(
                        title=mv.get("PositionTitle", ""),
                        location=location,
                        url=mv.get("PositionURI", ""),
                        description=mv.get("QualificationSummary", ""),
                        department=mv.get("OrganizationName", ""),
                        employment_type=mv.get("PositionSchedule", [{}])[0].get("Name"),
                        salary_text=sal_txt,
                        posted_at=start_date or None,
                        company_override=mv.get("DepartmentName", "US Government"),
                    )
                    if job:
                        jobs.append(job)

                count_so_far = data.get("SearchResult", {}).get("SearchResultCountAll", 0)
                if page * 25 >= count_so_far:
                    break
                page += 1

            log.info("[USAJobs] %s — %d jobs so far", keyword, len(jobs))

        log.info("[USAJobs] Total: %d US government jobs", len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# Scraper registry
# ─────────────────────────────────────────────────────────────────────────────

SCRAPER_REGISTRY: dict[str, type[BaseScraper]] = {
    "greenhouse":      GreenhouseScraper,
    "lever":           LeverScraper,
    "workday":         WorkdayScraper,
    "smartrecruiters": SmartRecruitersScraper,
    "ashby":           AshbyScraper,
    "themuse":         TheMuseScraper,
    "remotive":        RemotiveScraper,
    "usajobs":         USAJobsScraper,
    "html":            GenericHTMLScraper,
    "playwright":      PlaywrightScraper,
}


# ─────────────────────────────────────────────────────────────────────────────
# Deduplicator
# ─────────────────────────────────────────────────────────────────────────────

class JobDeduplicator:
    """
    Remove duplicate ``Job`` objects using their stable ``id`` fingerprint
    (SHA-256 of ``title + company + location``).

    Jobs scraped from multiple sources for the same posting are collapsed to
    the first-seen copy.
    """

    def __init__(self) -> None:
        self._seen: set[str] = set()

    def filter(self, jobs: list[Job]) -> list[Job]:
        unique: list[Job] = []
        for j in jobs:
            if j.id not in self._seen:
                self._seen.add(j.id)
                unique.append(j)
        return unique

    def reset(self) -> None:
        self._seen.clear()


# ─────────────────────────────────────────────────────────────────────────────
# Orchestrator — main public API
# ─────────────────────────────────────────────────────────────────────────────

class JobScrapeOrchestrator:
    """
    Runs a list of ``ScraperTarget`` configs through the appropriate scrapers,
    deduplicates results, and returns a ``list[dict]`` ready for JSON output.

    Usage::

        targets = [
            ScraperTarget(ats="greenhouse", company="stripe"),
            ScraperTarget(ats="ashby",      company="linear"),
        ]
        with JobScrapeOrchestrator() as orc:
            jobs = orc.run(targets)
        with open("jobs.json", "w") as f:
            json.dump(jobs, f, indent=2)
    """

    def __init__(
        self,
        client:       PoliteClient      | None = None,
        deduplicator: JobDeduplicator   | None = None,
    ) -> None:
        self._client = client      or PoliteClient()
        self._dedup  = deduplicator or JobDeduplicator()

    def run(self, targets: list[ScraperTarget]) -> list[dict[str, Any]]:
        all_jobs: list[Job] = []

        for target in targets:
            scraper_cls = SCRAPER_REGISTRY.get(target.ats.lower())
            if scraper_cls is None:
                log.error("Unknown ATS type '%s' — skipping %s", target.ats, target.company)
                continue

            scraper = scraper_cls(self._client, target)
            try:
                jobs = scraper.fetch_jobs()
                all_jobs.extend(jobs)
            except PermissionError as exc:
                log.warning("Blocked by robots.txt: %s", exc)
            except Exception as exc:
                log.error("Scraper failed (%s / %s): %s", target.ats, target.company, exc)

        unique = self._dedup.filter(all_jobs)
        log.info(
            "Scraping complete — %d unique US jobs (from %d total, %d duplicates removed)",
            len(unique), len(all_jobs), len(all_jobs) - len(unique),
        )
        return [j.to_dict() for j in unique]

    def close(self) -> None:
        self._client.close()

    def __enter__(self) -> "JobScrapeOrchestrator":
        return self

    def __exit__(self, *_: Any) -> None:
        self.close()


# ─────────────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────────────

# Built-in sample targets — all slugs verified live as of 2026-02
# Notes:
#   Greenhouse + Lever + Ashby use open public JSON APIs (no auth needed)
#   SmartRecruiters now requires a bearer token — excluded from defaults
#   Workday requires a browser session (Cloudflare + CSRF) — use PlaywrightScraper
_SAMPLE_TARGETS: list[dict[str, Any]] = [
    # ── Greenhouse (boards-api.greenhouse.io/v1/boards/{slug}/jobs) ──────────
    {"ats": "greenhouse", "company": "stripe",     "company_name": "Stripe"},
    {"ats": "greenhouse", "company": "airbnb",     "company_name": "Airbnb"},
    {"ats": "greenhouse", "company": "reddit",     "company_name": "Reddit"},
    {"ats": "greenhouse", "company": "coinbase",   "company_name": "Coinbase"},
    {"ats": "greenhouse", "company": "hubspot",    "company_name": "HubSpot"},
    {"ats": "greenhouse", "company": "brex",       "company_name": "Brex"},
    {"ats": "greenhouse", "company": "gitlab",     "company_name": "GitLab"},
    {"ats": "greenhouse", "company": "databricks", "company_name": "Databricks"},
    {"ats": "greenhouse", "company": "anthropic",  "company_name": "Anthropic"},
    {"ats": "greenhouse", "company": "figma",      "company_name": "Figma"},
    {"ats": "greenhouse", "company": "discord",    "company_name": "Discord"},
    {"ats": "greenhouse", "company": "asana",      "company_name": "Asana"},
    {"ats": "greenhouse", "company": "pinterest",  "company_name": "Pinterest"},
    # ── Lever (api.lever.co/v0/postings/{slug}) ──────────────────────────────
    {"ats": "lever", "company": "plaid",    "company_name": "Plaid"},
    {"ats": "lever", "company": "highspot", "company_name": "Highspot"},
    # ── Ashby (api.ashbyhq.com/posting-api/job-board/{slug}) ─────────────────
    {"ats": "ashby", "company": "linear",  "company_name": "Linear"},
    {"ats": "ashby", "company": "clerk",   "company_name": "Clerk"},
    {"ats": "ashby", "company": "loom",    "company_name": "Loom"},
    {"ats": "ashby", "company": "retool",  "company_name": "Retool"},
    # ── The Muse (themuse.com/api/public/jobs — free, no auth) ───────────────
    # Single entry fetches tech/data/product roles across all companies on platform
    {"ats": "themuse", "company": "themuse-aggregator", "company_name": "The Muse"},
    # ── Remotive (remotive.com/api/remote-jobs — free, no auth) ─────────────
    # Single entry fetches all remote tech jobs; US-hinted locations are kept
    {"ats": "remotive", "company": "remotive-aggregator", "company_name": "Remotive"},
    # ── USAJobs (data.usajobs.gov — free, requires API key + email) ──────────
    # Uncomment and fill in your credentials to enable government job listings:
    # {"ats": "usajobs", "company": "usajobs", "company_name": "USAJobs",
    #  "api_key": "YOUR_USAJOBS_API_KEY", "user_email": "your@email.com"},
]


def _load_targets(config_path: str | None) -> list[ScraperTarget]:
    if config_path:
        with open(config_path, encoding="utf-8") as f:
            raw = json.load(f)
    else:
        raw = _SAMPLE_TARGETS
    return [ScraperTarget(**r) for r in raw]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Production-ready US job listings scraper",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Example targets file (JSON array of objects):\n"
            '  [{"ats":"greenhouse","company":"stripe","company_name":"Stripe"}]\n\n'
            "Supported ATS values: greenhouse, lever, workday, smartrecruiters, ashby, "
            "themuse, remotive, usajobs, html, playwright"
        ),
    )
    parser.add_argument(
        "--config", "-c",
        metavar="FILE",
        help="Path to JSON targets config file (default: built-in sample targets)",
        default=None,
    )
    parser.add_argument(
        "--output", "-o",
        metavar="FILE",
        help="Write JSON output to this file instead of stdout",
        default=None,
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable DEBUG-level logging",
    )
    args = parser.parse_args()

    if args.verbose:
        logging.getLogger("job_scraper").setLevel(logging.DEBUG)

    targets = _load_targets(args.config)
    log.info("Loaded %d scrape target(s)", len(targets))

    with JobScrapeOrchestrator() as orc:
        jobs = orc.run(targets)

    output_json = json.dumps(jobs, indent=2, ensure_ascii=False)

    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(output_json)
        log.info("Wrote %d jobs to %s", len(jobs), args.output)
    else:
        print(output_json)


if __name__ == "__main__":
    main()
