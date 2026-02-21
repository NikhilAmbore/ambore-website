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
import os
import re
import time
import urllib.robotparser
import xml.etree.ElementTree as ET
from abc import ABC, abstractmethod
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
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
    # API credentials
    # api_key    → primary key / app_id / token
    # api_secret → secondary key / app_key (Adzuna, Apify input JSON)
    # user_email → required by USAJobs as the User-Agent / account email
    api_key:          str  = ""
    api_secret:       str  = ""
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
        force_usa:        bool       = False,   # bypass location filter (e.g. USAJobs)
    ) -> Job | None:
        """
        Normalise raw fields and return a ``Job``, or ``None`` if the listing
        is not in the USA (after applying the ``assume_us_remote`` heuristic).
        ``company_override`` lets aggregator scrapers (The Muse, Remotive, USAJobs)
        pass the real hiring-company name without changing ``target.company_name``.
        ``force_usa`` skips location filtering — use for sources that are
        inherently US-only (e.g. USAJobs.gov).
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

        if not is_usa and force_usa:
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

    Example — Salesforce:
        wd_tenant="salesforce"
        wd_site="External_Career_Site"
        wd_instance="wd12"
    → https://salesforce.wd12.myworkdayjobs.com/wday/cxs/
          salesforce/External_Career_Site/jobs

    The scraper first GETs the careers page to establish a session cookie and
    extract a CSRF token, then POSTs to the JSON search API.
    The API paginates in pages of 20.  Location is filtered post-fetch because
    Workday does not expose a query-time country filter on the public endpoint.
    """

    ATS_NAME = "workday"
    _API_TPL = (
        "https://{tenant}.{instance}.myworkdayjobs.com"
        "/wday/cxs/{tenant}/{site}/jobs"
    )
    _JOB_TPL = "https://{tenant}.{instance}.myworkdayjobs.com{path}"

    def _warm_session(self, tenant: str, instance: str, site: str) -> dict[str, str]:
        """
        GET the careers page to establish session cookies, then extract any
        CSRF token from cookies or inline JavaScript.  Returns extra headers
        to include in the subsequent POST request.

        Workday uses cookie ``CALYPSO_CSRF_TOKEN`` (confirmed 2026-02).
        The same cookie value must be sent as an ``X-Csrf-Token`` header.
        httpx's Client automatically forwards all cookies on subsequent
        requests to the same domain, so no manual cookie injection is needed.
        """
        page_url = (
            f"https://{tenant}.{instance}.myworkdayjobs.com/{site}/jobs"
        )
        extra: dict[str, str] = {}
        try:
            resp = self.client.get(
                page_url,
                headers={**DEFAULT_HEADERS,
                         "Accept": "text/html,application/xhtml+xml,*/*;q=0.8"},
            )
            # Workday CSRF cookie names (in priority order, most-specific first)
            for cname in (
                "CALYPSO_CSRF_TOKEN",   # confirmed Workday standard (2026)
                "csrfToken", "CSRF-TOKEN", "csrf_token", "_csrf", "csrf",
            ):
                tok = (resp.cookies.get(cname)
                       or self.client._client.cookies.get(cname))
                if tok:
                    extra["X-Csrf-Token"] = str(tok)
                    log.debug("[Workday] CSRF from cookie '%s' for %s/%s",
                              cname, tenant, site)
                    break

            # Fallback: scan inline <script> blocks
            if not extra:
                soup = BeautifulSoup(resp.text, "html.parser")
                for script in soup.find_all("script"):
                    text = script.get_text()
                    m = re.search(
                        r'''(?:csrfToken|CSRF)["\s]*[:=]\s*["']([^"']{10,})["']''',
                        text, re.IGNORECASE,
                    )
                    if m:
                        extra["X-Csrf-Token"] = m.group(1)
                        log.debug("[Workday] CSRF from inline script for %s/%s",
                                  tenant, site)
                        break

        except Exception as exc:
            log.debug("[Workday] session warmup skipped (%s/%s): %s",
                      tenant, site, exc)
        return extra

    def fetch_jobs(self) -> list[Job]:
        t = self.target
        if not t.wd_tenant or not t.wd_site:
            log.error("[Workday] wd_tenant and wd_site are required for %s", t.company)
            return []

        tenant   = t.wd_tenant
        site     = t.wd_site
        instance = t.wd_instance or "wd5"
        api_url  = self._API_TPL.format(tenant=tenant, site=site, instance=instance)

        log.info("[Workday] %s — warming session then fetching job list", tenant)

        # Establish session cookies + grab CSRF token before first POST
        extra_headers = self._warm_session(tenant, instance, site)

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
                    headers={"Content-Type": "application/json", **extra_headers},
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
                    force_usa=True,   # Workday targets are US-focused companies
                )
                if job:
                    jobs.append(job)

            offset += limit
            # Workday API: the 'total' field is unreliable after page 1 (may
            # return 0 even when more jobs exist).  Stop only when a page
            # returns fewer results than the page size — that is the true end.
            if len(postings) < limit:
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
        # Fall back to environment variables so GitHub Actions secrets work
        api_key = self.target.api_key or os.environ.get("USAJOBS_API_KEY", "")
        email   = self.target.user_email or os.environ.get("USAJOBS_EMAIL", "")
        if not api_key or not email:
            log.warning("[USAJobs] api_key / USAJOBS_API_KEY and user_email / USAJOBS_EMAIL "
                        "are required — skipping.  Register free at https://developer.usajobs.gov/")
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
                    # Build "City, ST" pairs; fall back to "Nationwide, US"
                    loc_parts = []
                    for l in locs:
                        city  = l.get("CityName", "").strip()
                        state = l.get("CountrySubDivisionCode", "").strip()
                        pair  = ", ".join(p for p in [city, state] if p)
                        if pair:
                            loc_parts.append(pair)
                    location = "; ".join(loc_parts) or "Nationwide, US"

                    pay = mv.get("PositionRemuneration", [{}])[0]
                    sal_min = float(pay.get("MinimumRange", 0) or 0) or None
                    sal_max = float(pay.get("MaximumRange", 0) or 0) or None
                    sal_txt = f"{int(sal_min)}-{int(sal_max)}" if sal_min else ""

                    start_date = mv.get("PublicationStartDate", "")

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
                        force_usa=True,   # USAJobs is 100% US — skip location filter
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
# RemoteOK  (public JSON API — no auth required)
# ─────────────────────────────────────────────────────────────────────────────

class RemoteOKScraper(BaseScraper):
    """
    RemoteOK public JSON API — https://remoteok.com/api
    No auth required.  Returns remote tech jobs; we keep US-hinted or
    worldwide/unspecified positions (treating them as US-eligible).
    """

    ATS_NAME = "remoteok"
    _API_URL  = "https://remoteok.com/api"

    # Location strings that indicate worldwide / US-eligible
    _US_HINTS = re.compile(
        r"\b(usa|united\s+states|u\.s|north\s+america|americas|worldwide|anywhere|global)\b",
        re.IGNORECASE,
    )

    def fetch_jobs(self) -> list[Job]:
        log.info("[RemoteOK] Fetching remote tech jobs")
        try:
            resp = self.client.get(self._API_URL)
            data = _safe_json(resp)
        except Exception as exc:
            log.error("[RemoteOK] Fetch failed: %s", exc)
            return []

        if isinstance(data, list) and data:
            data = data[1:]   # first element is metadata/legal notice

        jobs: list[Job] = []
        for raw in data:
            if not isinstance(raw, dict):
                continue

            title   = raw.get("position", "")
            company = raw.get("company", "")
            url     = raw.get("url", "")
            if not title or not url:
                continue

            location = (raw.get("location") or "").strip()
            tags     = raw.get("tags") or []
            desc_raw = raw.get("description", "") or ", ".join(str(t) for t in tags)

            is_usa, is_remote = _classify_location(location)
            is_remote = True   # all RemoteOK jobs are remote
            if not is_usa:
                loc_lower = location.lower()
                # Accept: blank, worldwide, "usa", explicit US phrases
                if (not loc_lower
                        or self._US_HINTS.search(loc_lower)
                        or "us" == loc_lower.strip("()")):
                    is_usa = True

            if not is_usa:
                continue

            salary_text = raw.get("salary", "") or ""
            posted_at   = raw.get("date") or None
            department  = str(tags[0]) if tags else None

            job = self._make_job(
                title=title,
                location=location or "Remote, US",
                url=url,
                description=_strip_html(str(desc_raw)),
                department=department,
                salary_text=str(salary_text),
                posted_at=posted_at,
                company_override=company,
            )
            if job:
                jobs.append(job)

        log.info("[RemoteOK] Total: %d US-eligible remote jobs", len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# WeWorkRemotely  (public RSS feeds — no auth required)
# ─────────────────────────────────────────────────────────────────────────────

class WeWorkRemotelyScraper(BaseScraper):
    """
    WeWorkRemotely RSS feeds — https://weworkremotely.com
    No auth required.  All jobs are remote; treated as US-eligible.
    Fetches programming, DevOps, product, design, and data science feeds.
    """

    ATS_NAME = "weworkremotely"
    _FEEDS: list[tuple[str, str]] = [
        ("https://weworkremotely.com/categories/remote-programming-jobs.rss",     "Engineering"),
        ("https://weworkremotely.com/categories/remote-devops-sysadmin-jobs.rss", "DevOps"),
        ("https://weworkremotely.com/categories/remote-product-jobs.rss",         "Product"),
        ("https://weworkremotely.com/categories/remote-design-jobs.rss",          "Design"),
        ("https://weworkremotely.com/categories/remote-full-stack-programming-jobs.rss", "Full Stack"),
    ]

    def fetch_jobs(self) -> list[Job]:
        log.info("[WeWorkRemotely] Fetching remote RSS feeds")
        jobs:  list[Job] = []
        seen:  set[str]  = set()

        for feed_url, category in self._FEEDS:
            if len(jobs) >= MAX_JOBS_PER_SRC:
                break
            try:
                resp = self.client.get(feed_url)
                root = ET.fromstring(resp.content)
            except Exception as exc:
                log.error("[WWR] %s — %s", feed_url, exc)
                continue

            channel = root.find("channel")
            if channel is None:
                continue

            for item in channel.findall("item"):
                link_el  = item.find("link")
                title_el = item.find("title")
                desc_el  = item.find("description")
                pub_el   = item.find("pubDate")
                guid_el  = item.find("guid")

                link      = (link_el.text  or "").strip() if link_el  is not None else ""
                title_raw = (title_el.text or "").strip() if title_el is not None else ""
                desc_raw  = (desc_el.text  or "").strip() if desc_el  is not None else ""
                pub_date  = (pub_el.text   or "").strip() if pub_el   is not None else ""
                guid      = (guid_el.text  or link).strip() if guid_el is not None else link

                if not link or guid in seen:
                    continue
                seen.add(guid)

                # WWR title format: "Company: Job Title"
                company = ""
                title   = title_raw
                if ": " in title_raw:
                    parts   = title_raw.split(": ", 1)
                    company = parts[0].strip()
                    title   = parts[1].strip()

                # Remove trailing " at Company" or " — Company"
                for sep in (" at ", " — ", " - "):
                    if sep in title:
                        title = title.rsplit(sep, 1)[0].strip()
                        break

                posted_at: str | None = None
                if pub_date:
                    try:
                        posted_at = parsedate_to_datetime(pub_date).isoformat()
                    except Exception:
                        posted_at = pub_date

                job = self._make_job(
                    title=title,
                    location="Remote, US",
                    url=link,
                    description=_strip_html(desc_raw),
                    department=category,
                    posted_at=posted_at,
                    company_override=company or self.target.company_name,
                )
                if job:
                    jobs.append(job)

            log.info("[WeWorkRemotely] %s — %d jobs so far", category, len(jobs))

        log.info("[WeWorkRemotely] Total: %d remote jobs", len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# BambooHR  (per-company public JSON board — no auth required)
# ─────────────────────────────────────────────────────────────────────────────

class BambooHRScraper(BaseScraper):
    """
    BambooHR public careers page scraper — https://{slug}.bamboohr.com/careers

    ``target.company`` must be the BambooHR subdomain slug (e.g. "procore").
    No auth required.  Parses the HTML careers page because the JSON endpoint
    (/careers/list) redirects to the BambooHR homepage.

    BambooHR careers page HTML structure:
      .BambooHR-ATS-Department-Item   — section per department
        .BambooHR-ATS-Department-Header  — department name (h4)
        .BambooHR-ATS-Jobs-Item          — individual job row (li)
          a[href]                         — job title + link
          .BambooHR-ATS-Location          — location text
    """

    ATS_NAME = "bamboohr"

    def fetch_jobs(self) -> list[Job]:
        slug = self.target.company
        url  = f"https://{slug}.bamboohr.com/careers"
        log.info("[BambooHR] %s — fetching careers HTML page", slug)

        try:
            resp = self.client.get(url, headers={"Accept": "text/html,*/*"})
            html = resp.text
        except Exception as exc:
            log.error("[BambooHR] %s — %s", slug, exc)
            return []

        soup = BeautifulSoup(html, "html.parser")
        jobs: list[Job] = []

        # Primary path: department sections containing job items
        dept_sections = soup.select(
            ".BambooHR-ATS-Department-Item, [class*='BambooHR-ATS-Department']"
        )
        if dept_sections:
            for section in dept_sections:
                dept_el    = section.select_one(
                    ".BambooHR-ATS-Department-Header, h4, h3"
                )
                department = dept_el.get_text(strip=True) if dept_el else None
                for item in section.select(
                    ".BambooHR-ATS-Jobs-Item, li"
                ):
                    self._parse_bamboo_item(item, slug, department, jobs)
        else:
            # Flat-list fallback — sometimes BambooHR renders a simple <ul>
            for item in soup.select(
                ".BambooHR-ATS-Jobs-Item, li[class*='job'], li[class*='opening']"
            ):
                self._parse_bamboo_item(item, slug, None, jobs)

        log.info("[BambooHR] %s — %d US jobs", slug, len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]

    def _parse_bamboo_item(
        self,
        item: "Tag",
        slug: str,
        department: str | None,
        jobs: list[Job],
    ) -> None:
        link = item.find("a", href=True)
        if not link:
            return
        title = link.get_text(strip=True)
        if not title:
            return

        job_url = urljoin(f"https://{slug}.bamboohr.com", str(link["href"]))

        loc_el   = item.select_one(
            ".BambooHR-ATS-Location, [class*='location'], [class*='Location']"
        )
        location = loc_el.get_text(strip=True) if loc_el else "US"

        job = self._make_job(
            title=title,
            location=location or "US",
            url=job_url,
            department=department,
        )
        if job:
            jobs.append(job)


# ─────────────────────────────────────────────────────────────────────────────
# Workable  (per-company public JSON API — no auth required)
# ─────────────────────────────────────────────────────────────────────────────

class WorkableScraper(BaseScraper):
    """
    Workable public jobs API — https://apply.workable.com/api/v3/accounts/{slug}/jobs

    ``target.company`` must be the Workable account slug (e.g. "typeform").
    No auth required.  Paginated via cursor token.
    """

    ATS_NAME = "workable"

    def fetch_jobs(self) -> list[Job]:
        slug = self.target.company
        api_url = f"https://apply.workable.com/api/v3/accounts/{slug}/jobs"
        log.info("[Workable] %s — fetching job list", slug)

        jobs:  list[Job] = []
        token: str | None = None

        while True:
            body: dict[str, Any] = {
                "query": "",
                "location": [],
                "department": [],
                "worktype": [],
                "remote": [],
            }
            if token:
                body["token"] = token

            try:
                resp = self.client._client.post(
                    api_url,
                    json=body,
                    headers={**DEFAULT_HEADERS, "Content-Type": "application/json"},
                    timeout=REQUEST_TIMEOUT,
                )
                resp.raise_for_status()
                data = _safe_json(resp)
            except Exception as exc:
                log.error("[Workable] %s — %s", slug, exc)
                break

            for raw in data.get("results", []):
                city     = raw.get("city",    "") or ""
                state    = raw.get("state",   "") or ""
                country  = (raw.get("country", "") or "").upper()
                workplace = raw.get("workplace", "") or ""
                remote   = workplace.lower() == "remote" or bool(raw.get("remote"))

                parts = [p for p in [city, state, country] if p]
                location = ", ".join(parts) if parts else ("Remote" if remote else "")

                is_usa, is_remote = _classify_location(location)
                if remote:
                    is_remote = True
                    if not is_usa:
                        is_usa = True
                if not is_usa and country in ("US", "USA", "UNITED STATES"):
                    is_usa = True

                if not is_usa:
                    continue

                shortcode = raw.get("shortcode", "")
                job_url   = f"https://apply.workable.com/{slug}/j/{shortcode}"

                job = self._make_job(
                    title=raw.get("title", ""),
                    location=location or "US",
                    url=job_url,
                    department=raw.get("department"),
                    employment_type=raw.get("employment_type"),
                )
                if job:
                    jobs.append(job)

            token = data.get("token")
            if not token or len(jobs) >= MAX_JOBS_PER_SRC:
                break

        log.info("[Workable] %s — %d US jobs", slug, len(jobs))
        return jobs


# ─────────────────────────────────────────────────────────────────────────────
# Adzuna  (free developer API — register at https://developer.adzuna.com/)
# ─────────────────────────────────────────────────────────────────────────────

class AdzunaScraper(BaseScraper):
    """
    Adzuna US Jobs API — https://api.adzuna.com/v1/api/jobs/us/search/{page}

    Free developer plan: up to 250 req/min.
    Register at https://developer.adzuna.com/ to get app_id + app_key.

    Credentials resolution order (first non-empty wins):
      1. target.api_key  + target.api_secret
      2. ADZUNA_APP_ID   + ADZUNA_APP_KEY  (environment variables)

    Aggregator — a single target entry scrapes many keyword categories.
    """

    ATS_NAME = "adzuna"
    _BASE    = "https://api.adzuna.com/v1/api/jobs/us/search"

    # Broad keyword sweep — Adzuna returns US-filtered results for all
    _KEYWORDS = [
        "software engineer", "backend engineer", "frontend engineer",
        "full stack engineer", "data engineer", "data scientist",
        "machine learning engineer", "devops engineer", "cloud engineer",
        "site reliability engineer", "platform engineer", "security engineer",
        "mobile engineer", "ios developer", "android developer",
        "product manager", "ux designer", "it specialist",
    ]

    def fetch_jobs(self) -> list[Job]:
        app_id  = self.target.api_key    or os.environ.get("ADZUNA_APP_ID",  "")
        app_key = self.target.api_secret or os.environ.get("ADZUNA_APP_KEY", "")
        if not app_id or not app_key:
            log.warning("[Adzuna] ADZUNA_APP_ID and ADZUNA_APP_KEY required "
                        "— register free at https://developer.adzuna.com/")
            return []

        log.info("[Adzuna] Fetching US tech jobs")
        jobs: list[Job] = []
        seen: set[str]  = set()

        for keyword in self._KEYWORDS:
            if len(jobs) >= MAX_JOBS_PER_SRC:
                break
            page = 1
            while len(jobs) < MAX_JOBS_PER_SRC:
                try:
                    resp = self.client.get(
                        f"{self._BASE}/{page}",
                        params={
                            "app_id":           app_id,
                            "app_key":          app_key,
                            "results_per_page": 50,
                            "what":             keyword,
                            "where":            "united states",
                            "content-type":     "application/json",
                        },
                    )
                    data = _safe_json(resp)
                except Exception as exc:
                    log.error("[Adzuna] %s p%d — %s", keyword, page, exc)
                    break

                results = data.get("results", [])
                if not results:
                    break

                for raw in results:
                    job_id = raw.get("id", "")
                    if job_id in seen:
                        continue
                    seen.add(job_id)

                    title    = raw.get("title", "")
                    company  = (raw.get("company") or {}).get("display_name", "")
                    location = (raw.get("location") or {}).get("display_name", "")
                    url      = raw.get("redirect_url", "")
                    desc_raw = raw.get("description", "")
                    sal_min  = raw.get("salary_min") or None
                    sal_max  = raw.get("salary_max") or None
                    created  = raw.get("created")    or None

                    # Adzuna is queried with where=united+states so all results
                    # are US jobs — use force_usa to bypass _classify_location()
                    # which rejects location strings without a 2-letter state code
                    # (e.g. "West, McLennan County", "New York City")
                    salary_text = ""
                    if sal_min or sal_max:
                        salary_text = f"{int(sal_min or 0)}-{int(sal_max or 0)}"

                    job = self._make_job(
                        title=title,
                        location=location or "US",
                        url=url,
                        description=_strip_html(desc_raw),
                        department=keyword.title(),
                        employment_type=raw.get("contract_type"),
                        salary_text=salary_text,
                        posted_at=created,
                        company_override=company,
                        force_usa=True,
                    )
                    if job:
                        if sal_min:
                            job.salary_min = float(sal_min)
                        if sal_max:
                            job.salary_max = float(sal_max)
                        jobs.append(job)

                total   = data.get("count", 0)
                fetched = page * 50
                if fetched >= total or fetched >= 200:   # cap 4 pages per keyword
                    break
                page += 1

            log.info("[Adzuna] %s — %d jobs so far", keyword, len(jobs))

        log.info("[Adzuna] Total: %d US jobs", len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# SerpAPI — Google Jobs  (https://serpapi.com, free tier: 100 searches/month)
# ─────────────────────────────────────────────────────────────────────────────

class SerpAPIGoogleJobsScraper(BaseScraper):
    """
    Google Jobs via SerpAPI — https://serpapi.com/google-jobs-api

    Free plan: 100 searches / month.  Paid plans start at $50/mo.
    Register at https://serpapi.com/ and get your API key.

    Credentials resolution order:
      1. target.api_key
      2. SERPAPI_KEY  (environment variable)

    Searches multiple tech keywords across the US.
    """

    ATS_NAME = "serpapi"
    _BASE    = "https://serpapi.com/search.json"
    _KEYWORDS = [
        "software engineer", "data scientist", "machine learning engineer",
        "devops engineer", "cloud architect", "frontend developer",
        "backend developer", "full stack developer", "data engineer",
        "cybersecurity analyst", "product manager", "mobile developer",
    ]

    def fetch_jobs(self) -> list[Job]:
        api_key = self.target.api_key or os.environ.get("SERPAPI_KEY", "")
        if not api_key:
            log.warning("[SerpAPI] SERPAPI_KEY required — "
                        "register free at https://serpapi.com/")
            return []

        log.info("[SerpAPI] Fetching Google Jobs")
        jobs: list[Job] = []
        seen: set[str]  = set()

        for keyword in self._KEYWORDS:
            if len(jobs) >= MAX_JOBS_PER_SRC:
                break
            start = 0
            while len(jobs) < MAX_JOBS_PER_SRC:
                try:
                    resp = self.client.get(
                        self._BASE,
                        params={
                            "engine":   "google_jobs",
                            "q":        keyword,
                            "location": "United States",
                            "hl":       "en",
                            "gl":       "us",
                            "start":    start,
                            "api_key":  api_key,
                        },
                    )
                    data = _safe_json(resp)
                except Exception as exc:
                    log.error("[SerpAPI] %s start=%d — %s", keyword, start, exc)
                    break

                # SerpAPI returns error object when quota exhausted
                if "error" in data:
                    log.warning("[SerpAPI] API error: %s", data["error"])
                    break

                results = data.get("jobs_results", [])
                if not results:
                    break

                for raw in results:
                    uid = raw.get("job_id", raw.get("title", "") + raw.get("company_name", ""))
                    if uid in seen:
                        continue
                    seen.add(uid)

                    title    = raw.get("title", "")
                    company  = raw.get("company_name", "")
                    location = raw.get("location", "")
                    url      = (raw.get("related_links") or [{}])[0].get("link", "")
                    desc_raw = raw.get("description", "")
                    posted   = (raw.get("detected_extensions") or {}).get("posted_at")

                    is_usa, is_remote = _classify_location(location)
                    if not is_usa:
                        # Google Jobs US results are always US; trust the query
                        is_usa = True

                    # Salary from highlights
                    sal_text = ""
                    for section in (raw.get("job_highlights") or []):
                        if "alary" in section.get("title", ""):
                            items = section.get("items", [])
                            if items:
                                sal_text = items[0]
                            break

                    job = self._make_job(
                        title=title,
                        location=location or "US",
                        url=url,
                        description=_strip_html(desc_raw),
                        department=keyword.title(),
                        salary_text=sal_text,
                        posted_at=posted,
                        company_override=company,
                    )
                    if job:
                        jobs.append(job)

                # SerpAPI paginates in steps of 10
                if len(results) < 10 or start >= 30:   # cap 4 pages
                    break
                start += 10

            log.info("[SerpAPI/Google] %s — %d jobs so far", keyword, len(jobs))

        log.info("[SerpAPI/Google] Total: %d US jobs", len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# Apify  (https://apify.com — free tier: $5 platform credits / month)
# ─────────────────────────────────────────────────────────────────────────────

class ApifyJobsScraper(BaseScraper):
    """
    Apify cloud scraping platform — runs pre-built actors to extract jobs
    from sources that require JS rendering (Indeed, LinkedIn, Glassdoor, etc.)

    Free tier: $5/month in platform credits.
    Register at https://apify.com/ and get your API token.

    Credentials resolution order:
      1. target.api_key
      2. APIFY_TOKEN  (environment variable)

    ``target.company`` is used as the Apify Actor ID.
    ``target.api_secret`` (or APIFY_ACTOR_INPUT env var) is a JSON string of
    actor input — if omitted a sensible default for US tech jobs is used.

    Common actor IDs for US job scraping:
      bebity/linkedin-jobs-scraper      — LinkedIn (fast, popular)
      misceres/indeed-scraper           — Indeed
      curious_coder/glassdoor-scraper   — Glassdoor
      compass/google-jobs-scraper       — Google Jobs (alternative to SerpAPI)
    """

    ATS_NAME  = "apify"
    _BASE_URL = "https://api.apify.com/v2/acts"

    # Default actor input for generic job actors
    _DEFAULT_INPUT: dict[str, Any] = {
        "location":         "United States",
        "country":          "US",
        "maxItems":         200,
        "proxy":            {"useApifyProxy": True},
    }

    def fetch_jobs(self) -> list[Job]:
        token    = self.target.api_key or os.environ.get("APIFY_TOKEN", "")
        actor_id = self.target.company   # e.g. "bebity/linkedin-jobs-scraper"

        if not token:
            log.warning("[Apify] APIFY_TOKEN required — register at https://apify.com/")
            return []
        if not actor_id or actor_id == "apify-aggregator":
            log.warning("[Apify] target.company must be an Apify actor ID "
                        "(e.g. 'bebity/linkedin-jobs-scraper')")
            return []

        # Actor input — target.api_secret may override as JSON string
        actor_input: dict[str, Any] = dict(self._DEFAULT_INPUT)
        raw_input = self.target.api_secret or os.environ.get("APIFY_ACTOR_INPUT", "")
        if raw_input:
            try:
                actor_input.update(json.loads(raw_input))
            except json.JSONDecodeError:
                log.warning("[Apify] Invalid APIFY_ACTOR_INPUT JSON — using defaults")

        run_url = f"{self._BASE_URL}/{actor_id}/run-sync-get-dataset-items"
        log.info("[Apify] Running actor %s", actor_id)

        try:
            # run-sync-get-dataset-items: POSTs input, waits for run, returns items
            resp = self.client._client.post(
                run_url,
                params={"token": token, "format": "json", "clean": "true"},
                json=actor_input,
                headers={**DEFAULT_HEADERS, "Content-Type": "application/json"},
                timeout=300,   # actor runs can take several minutes
            )
            resp.raise_for_status()
            items = _safe_json(resp)
        except Exception as exc:
            log.error("[Apify] Actor %s failed: %s", actor_id, exc)
            return []

        if not isinstance(items, list):
            items = items.get("items", []) if isinstance(items, dict) else []

        log.info("[Apify] Actor returned %d raw items", len(items))
        jobs: list[Job] = []

        for raw in items:
            if not isinstance(raw, dict):
                continue

            # Normalise across different actor schemas
            title   = (raw.get("title")   or raw.get("positionName")  or
                       raw.get("jobTitle") or raw.get("name", ""))
            company = (raw.get("company") or raw.get("companyName")    or
                       raw.get("employer") or "")
            location= (raw.get("location") or raw.get("place")         or
                       raw.get("jobLocation") or "")
            url     = (raw.get("url")      or raw.get("jobUrl")        or
                       raw.get("applyUrl")  or raw.get("link", ""))
            desc    = (raw.get("description") or raw.get("jobDescription") or "")
            dept    = (raw.get("department")  or raw.get("category")       or "")
            emp_type= (raw.get("employmentType") or raw.get("jobType")     or "")
            posted  = (raw.get("postedAt")   or raw.get("publishedAt")     or
                       raw.get("datePosted") or None)
            sal_raw = (raw.get("salary")     or raw.get("salaryRange")     or "")

            if not title or not url:
                continue

            is_usa, is_remote = _classify_location(str(location))
            if not is_usa:
                # Apify actors are configured for US; trust if no country detected
                if not location or str(location).strip().upper() in ("US", "USA", "REMOTE"):
                    is_usa = True
            if not is_usa:
                continue

            job = self._make_job(
                title=str(title),
                location=str(location) or "US",
                url=str(url),
                description=_strip_html(str(desc)),
                department=str(dept) or None,
                employment_type=str(emp_type) or None,
                salary_text=str(sal_raw),
                posted_at=str(posted) if posted else None,
                company_override=str(company) or None,
            )
            if job:
                jobs.append(job)

        log.info("[Apify] %s — %d US jobs", actor_id, len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# iCIMS  (public HTML — no auth required)
# ─────────────────────────────────────────────────────────────────────────────

class ICIMSScraper(BaseScraper):
    """
    iCIMS career page HTML scraper.

    iCIMS renders a consistent HTML structure for its job listing pages.
    Set ``target.careers_url`` to the company's public iCIMS job search URL.

    Common URL patterns
    -------------------
    Per-company numeric portal:
      https://{id}.icims.com/jobs/search?ss=1&searchRelation=keyword_all
    Custom company career domain:
      https://careers.{company}.com/search-jobs  (behind iCIMS)

    iCIMS HTML job row selectors (tried in order):
      .iCIMS_Expandable_Container  — most common widget layout
      .iCIMS_JobsTable_Cell        — table-based layout
      .job-listing-item            — some custom themes
    """

    ATS_NAME = "icims"

    # iCIMS-specific selectors tried in priority order
    _CONTAINER_SELECTORS = [
        ".iCIMS_Expandable_Container",
        ".iCIMS_JobsTable_Cell",
        "tr.iCIMS_JobsTable_Row",
        ".job-listing-item",
        "[data-field='jobtitle']",
    ]
    _LOC_SELECTORS = [
        ".iCIMS_Location",
        "[class*='iCIMS_Location']",
        "[class*='location']",
        "td:nth-child(2)",
    ]
    _TYPE_SELECTORS = [
        ".iCIMS_Type",
        "[class*='iCIMS_Type']",
        "[class*='employment']",
        "[class*='type']",
    ]

    def fetch_jobs(self) -> list[Job]:
        url = self.target.careers_url
        if not url:
            log.error("[iCIMS] careers_url is required for %s", self.target.company)
            return []

        log.info("[iCIMS] %s — fetching %s", self.target.company_name, url)
        try:
            resp = self.client.get(url)
            html = resp.text
        except Exception as exc:
            log.error("[iCIMS] %s — %s", url, exc)
            return []

        soup     = BeautifulSoup(html, "html.parser")
        parsed   = urlparse(url)
        base_url = f"{parsed.scheme}://{parsed.netloc}"
        jobs: list[Job] = []

        # Try iCIMS-specific containers first
        containers: list["Tag"] = []
        for sel in self._CONTAINER_SELECTORS:
            found = soup.select(sel)
            if found:
                containers = found
                log.debug("[iCIMS] matched selector: %s (%d items)", sel, len(found))
                break

        if containers:
            for container in containers[:MAX_JOBS_PER_SRC]:
                link = container.find("a", href=True)
                if not link:
                    continue
                title = link.get_text(strip=True)
                if not title:
                    continue

                job_url = urljoin(base_url, str(link["href"]))

                loc_el   = self._first_el(container, self._LOC_SELECTORS)
                location = loc_el.get_text(strip=True) if loc_el else "US"

                type_el  = self._first_el(container, self._TYPE_SELECTORS)
                emp_type = type_el.get_text(strip=True) if type_el else None

                job = self._make_job(
                    title=title,
                    location=location or "US",
                    url=job_url,
                    employment_type=emp_type,
                )
                if job:
                    jobs.append(job)
        else:
            # Generic HTML fallback — same heuristics as GenericHTMLScraper
            log.debug("[iCIMS] no iCIMS selectors matched — using generic HTML fallback")
            delegate = GenericHTMLScraper(self.client, self.target)
            items    = delegate._find_job_elements(soup)
            for item in items[:MAX_JOBS_PER_SRC]:
                title    = delegate._first_text(item, GenericHTMLScraper._TITLE_SELECTORS)
                location = delegate._first_text(item, GenericHTMLScraper._LOCATION_SELECTORS)
                link_tag = item.find("a", href=True) if item.name != "a" else item
                job_url  = urljoin(base_url, str(link_tag["href"])) if link_tag else url
                if not title:
                    continue
                job = self._make_job(
                    title=title, location=location or "US", url=job_url,
                )
                if job:
                    jobs.append(job)

        log.info("[iCIMS] %s — %d US jobs", self.target.company_name, len(jobs))
        return jobs

    @staticmethod
    def _first_el(container: "Tag", selectors: list[str]) -> "Tag | None":
        for sel in selectors:
            el = container.select_one(sel)
            if el:
                return el
        return None


# ─────────────────────────────────────────────────────────────────────────────
# Oracle Taleo  (public HTML — no auth required)
# ─────────────────────────────────────────────────────────────────────────────

class TaleoScraper(BaseScraper):
    """
    Oracle Taleo career page HTML scraper.

    Taleo generates fairly consistent HTML for its job search pages.
    Set ``target.careers_url`` to the Taleo job search page URL.

    Common URL pattern:
      https://{tenant}.taleo.net/careersection/{section}/jobsearch.ftl

    Note: many companies have migrated from Taleo to Oracle HCM Cloud.
    If the careers_url returns an error, the company may have changed ATS.

    Taleo HTML selectors:
      tr[class*='listSectionContentTD']  — job rows in table view
      tr.even / tr.odd                   — alternating row classes
      .jobListItem                       — modern widget view
    """

    ATS_NAME = "taleo"

    _ROW_SELECTORS = [
        "tr.listSectionContentTD",
        "tr.even, tr.odd",
        ".jobListItem",
        ".job-list-item",
        "[class*='jobListItem']",
    ]

    def fetch_jobs(self) -> list[Job]:
        url = self.target.careers_url
        if not url:
            log.error("[Taleo] careers_url is required for %s", self.target.company)
            return []

        log.info("[Taleo] %s — fetching %s", self.target.company_name, url)
        try:
            resp = self.client.get(url)
            html = resp.text
        except Exception as exc:
            log.error("[Taleo] %s — %s", url, exc)
            return []

        soup     = BeautifulSoup(html, "html.parser")
        parsed   = urlparse(url)
        base_url = f"{parsed.scheme}://{parsed.netloc}"
        jobs: list[Job] = []

        rows: list["Tag"] = []
        for sel in self._ROW_SELECTORS:
            found = soup.select(sel)
            if found:
                rows = found
                log.debug("[Taleo] matched selector: %s (%d rows)", sel, len(found))
                break

        if rows:
            for row in rows[:MAX_JOBS_PER_SRC]:
                link = row.find("a", href=True)
                if not link:
                    continue
                title = link.get_text(strip=True)
                if not title:
                    continue

                job_url = urljoin(base_url, str(link["href"]))

                # Taleo location is usually the 3rd <td> or a cell with "location" class
                loc_el = (
                    row.select_one(
                        "td[class*='location'], td[class*='Location'], "
                        "[class*='location']"
                    )
                    or (row.select("td")[2] if len(row.select("td")) > 2 else None)
                )
                location = loc_el.get_text(strip=True) if loc_el else "US"

                job = self._make_job(
                    title=title,
                    location=location or "US",
                    url=job_url,
                )
                if job:
                    jobs.append(job)
        else:
            # Generic HTML fallback
            log.debug("[Taleo] no Taleo-specific rows found — using generic HTML fallback")
            delegate = GenericHTMLScraper(self.client, self.target)
            items    = delegate._find_job_elements(soup)
            for item in items[:MAX_JOBS_PER_SRC]:
                title    = delegate._first_text(item, GenericHTMLScraper._TITLE_SELECTORS)
                location = delegate._first_text(item, GenericHTMLScraper._LOCATION_SELECTORS)
                link_tag = item.find("a", href=True) if item.name != "a" else item
                job_url  = urljoin(base_url, str(link_tag["href"])) if link_tag else url
                if not title:
                    continue
                job = self._make_job(
                    title=title, location=location or "US", url=job_url,
                )
                if job:
                    jobs.append(job)

        log.info("[Taleo] %s — %d US jobs", self.target.company_name, len(jobs))
        return jobs


# ─────────────────────────────────────────────────────────────────────────────
# LinkedIn Guest API  (no login · no API key · completely free)
# ─────────────────────────────────────────────────────────────────────────────

class LinkedInGuestScraper(BaseScraper):
    """
    Scrapes LinkedIn jobs via the public guest API — no login, no API key.

    Two unauthenticated LinkedIn endpoints (same ones used by the public
    https://www.linkedin.com/jobs/search page before you log in):
      1. GET /jobs-guest/jobs/api/seeMoreJobPostings/search
         → Returns an HTML fragment of job cards for a keyword + location.
      2. GET /jobs-guest/jobs/api/jobPosting/{id}
         → Returns full job detail HTML for a single posting.

    target.company     — primary keyword  (e.g. "software engineer")
    target.api_secret  — optional JSON array of additional keywords:
                         '["data scientist","product manager","devops engineer"]'
    """

    ATS_NAME    = "linkedin"
    _SEARCH_URL = "https://www.linkedin.com/jobs-guest/jobs/api/seeMoreJobPostings/search"
    _DETAIL_URL = "https://www.linkedin.com/jobs-guest/jobs/api/jobPosting/{id}"
    _GEO_ID     = "103644278"   # United States
    _PAGE_SIZE  = 25
    _MAX_PAGES  = 4             # 4 × 25 = up to 100 results per keyword

    _HEADERS: dict[str, str] = {
        "User-Agent":         "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                              "AppleWebKit/537.36 (KHTML, like Gecko) "
                              "Chrome/124.0.0.0 Safari/537.36",
        "Accept":             "*/*",
        "Accept-Language":    "en-US,en;q=0.9",
        "csrf-token":         "ajax:0000000000000000000",
        "sec-ch-ua":          '"Chromium";v="124", "Google Chrome";v="124"',
        "sec-ch-ua-mobile":   "?0",
        "sec-ch-ua-platform": '"macOS"',
        "sec-fetch-dest":     "empty",
        "sec-fetch-mode":     "cors",
        "sec-fetch-site":     "same-origin",
        "Referer":            "https://www.linkedin.com/jobs/search"
                              "?keywords=software+engineer&location=United+States",
    }

    def _search_page(self, keyword: str, start: int) -> list[str]:
        """Return job IDs from one search result page."""
        params: dict[str, str] = {
            "keywords": keyword,
            "location": "United States",
            "geoId":    self._GEO_ID,
            "f_TPR":    "r604800",   # last 7 days
            "start":    str(start),
        }
        try:
            resp = self.client.get(self._SEARCH_URL, params=params,
                                   headers=self._HEADERS)
            resp.raise_for_status()
        except Exception as exc:
            log.debug("[LinkedIn] search error (kw=%r start=%d): %s", keyword, start, exc)
            return []

        soup = BeautifulSoup(resp.text, "html.parser")
        ids: list[str] = []
        for card in soup.select(".job-search-card"):
            urn = card.get("data-entity-urn", "")
            job_id = urn.split(":")[-1] if ":" in urn else ""
            if job_id and job_id.isdigit():
                ids.append(job_id)
        return ids

    def _fetch_detail(self, job_id: str) -> Job | None:
        """Parse a single job posting page into a Job object."""
        url = self._DETAIL_URL.format(id=job_id)
        try:
            resp = self.client.get(url, headers=self._HEADERS)
            resp.raise_for_status()
        except Exception as exc:
            log.debug("[LinkedIn] detail error (id=%s): %s", job_id, exc)
            return None

        soup = BeautifulSoup(resp.text, "html.parser")

        title_el   = (soup.select_one(".topcard__title") or
                      soup.select_one(".top-card-layout__title"))
        company_el = (soup.select_one(".topcard__org-name-link") or
                      soup.select_one(".top-card-layout__company"))
        loc_el     = (soup.select_one(".topcard__flavor--bullet") or
                      soup.select_one(".top-card-layout__first-subline"))
        desc_el    = (soup.select_one(".show-more-less-html__markup") or
                      soup.select_one(".description__text"))
        posted_el  = (soup.select_one(".posted-time-ago__text") or
                      soup.select_one("time"))
        link_el    = (soup.select_one("a.topcard__link") or
                      soup.select_one('a[href*="/jobs/view/"]'))

        title_str   = title_el.get_text(strip=True)                   if title_el   else ""
        company_str = company_el.get_text(strip=True)                 if company_el else ""
        loc_str     = loc_el.get_text(strip=True).replace("\n", " ")  if loc_el     else ""
        desc_str    = _strip_html(str(desc_el))                       if desc_el    else ""
        job_url     = (link_el.get("href", "").split("?")[0]          if link_el    else
                       f"https://www.linkedin.com/jobs/view/{job_id}")
        posted_str: str | None = None
        if posted_el:
            posted_str = (posted_el.get("datetime") or
                          posted_el.get_text(strip=True) or None)

        # Employment type from criteria items
        emp_type = ""
        for item in soup.select(".description__job-criteria-item"):
            lbl = item.select_one(".description__job-criteria-subheader")
            val = item.select_one(".description__job-criteria-text--criteria")
            if lbl and val and "employment" in lbl.get_text(strip=True).lower():
                emp_type = val.get_text(strip=True)
                break

        if not title_str or not job_url:
            return None

        # Guest API filters to US via geoId — trust when location is ambiguous
        is_usa, _ = _classify_location(loc_str)
        if (not is_usa and loc_str
                and "united states" not in loc_str.lower()
                and "remote" not in loc_str.lower()):
            return None

        return self._make_job(
            title=title_str,
            location=loc_str or "United States",
            url=job_url,
            description=desc_str,
            department=None,
            employment_type=emp_type or None,
            salary_text="",
            posted_at=str(posted_str) if posted_str else None,
            company_override=company_str or None,
        )

    def fetch_jobs(self) -> list[Job]:
        # Resolve keyword list
        keywords: list[str] = []
        raw = self.target.api_secret
        if raw:
            try:
                parsed = json.loads(raw)
                if isinstance(parsed, list):
                    keywords = [str(k) for k in parsed if k]
                elif isinstance(parsed, str):
                    keywords = [parsed]
            except json.JSONDecodeError:
                keywords = [raw]
        if self.target.company and self.target.company not in keywords:
            keywords.insert(0, self.target.company)
        if not keywords:
            keywords = ["software engineer"]

        seen_ids: set[str] = set()
        jobs: list[Job] = []

        for kw in keywords:
            log.info("[LinkedIn] searching: %r", kw)
            for page in range(self._MAX_PAGES):
                ids = self._search_page(kw, page * self._PAGE_SIZE)
                if not ids:
                    break
                new_ids = [i for i in ids if i not in seen_ids]
                seen_ids.update(new_ids)
                for job_id in new_ids:
                    job = self._fetch_detail(job_id)
                    if job:
                        jobs.append(job)
                    time.sleep(0.4)   # be polite to LinkedIn's guest servers
                    if len(jobs) >= MAX_JOBS_PER_SRC:
                        break
                if len(jobs) >= MAX_JOBS_PER_SRC or len(ids) < self._PAGE_SIZE:
                    break

        log.info("[LinkedIn] %d US jobs collected", len(jobs))
        return jobs[:MAX_JOBS_PER_SRC]


# ─────────────────────────────────────────────────────────────────────────────
# Scraper registry
# ─────────────────────────────────────────────────────────────────────────────

SCRAPER_REGISTRY: dict[str, type[BaseScraper]] = {
    # ── ATS platforms (per-company) ────────────────────────────────────────
    "greenhouse":      GreenhouseScraper,
    "lever":           LeverScraper,
    "workday":         WorkdayScraper,
    "smartrecruiters": SmartRecruitersScraper,
    "ashby":           AshbyScraper,
    "bamboohr":        BambooHRScraper,
    "workable":        WorkableScraper,
    "icims":           ICIMSScraper,
    "taleo":           TaleoScraper,
    # ── Aggregator APIs (single entry fetches many companies) ──────────────
    "themuse":         TheMuseScraper,
    "remotive":        RemotiveScraper,
    "remoteok":        RemoteOKScraper,
    "weworkremotely":  WeWorkRemotelyScraper,
    "usajobs":         USAJobsScraper,      # free API key required
    "adzuna":          AdzunaScraper,       # free API key required
    "serpapi":         SerpAPIGoogleJobsScraper,  # Google Jobs; free key required
    "apify":           ApifyJobsScraper,    # cloud actors; free tier available
    "linkedin":        LinkedInGuestScraper, # LinkedIn guest API — no key needed
    # ── Generic fallbacks ──────────────────────────────────────────────────
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

    def run(
        self,
        targets:    list[ScraperTarget],
        since_hours: int | None = None,
    ) -> list[dict[str, Any]]:
        """
        Scrape all targets and return normalised job dicts.

        Args:
            targets:     List of scrape targets to run.
            since_hours: When set, exclude jobs whose ``posted_at`` is older
                         than this many hours.  Jobs with no ``posted_at`` date
                         are always included (most ATS APIs omit posting dates).
        """
        all_jobs: list[Job] = []
        cutoff: datetime | None = None
        if since_hours is not None:
            cutoff = datetime.now(timezone.utc) - timedelta(hours=since_hours)
            log.info("Date filter: keeping jobs posted since %s", cutoff.isoformat())

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

        # Optional date filter — only applied when since_hours is set
        if cutoff is not None:
            before = len(unique)
            def _is_recent(j: Job) -> bool:
                if not j.posted_at:
                    return True   # no date → include
                try:
                    dt = datetime.fromisoformat(j.posted_at)
                    if dt.tzinfo is None:
                        dt = dt.replace(tzinfo=timezone.utc)
                    return dt >= cutoff  # type: ignore[operator]
                except Exception:
                    return True   # unparseable date → include
            unique = [j for j in unique if _is_recent(j)]
            log.info("Date filter: %d → %d jobs (removed %d older than %dh)",
                     before, len(unique), before - len(unique), since_hours)

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
#   Workday: CSRF is auto-handled via session warmup GET before each POST
#   SmartRecruiters: public API locked; requires company smart_token (commented out)
#   BambooHR: careers pages are JS-rendered (React SPA) — needs Playwright
#   iCIMS / Taleo: HTML scrapers; effectiveness depends on page structure
_SAMPLE_TARGETS: list[dict[str, Any]] = [
    # ── Greenhouse (boards-api.greenhouse.io/v1/boards/{slug}/jobs) ──────────
    # All slugs verified 2026-02
    # Fintech
    {"ats": "greenhouse", "company": "stripe",       "company_name": "Stripe"},
    {"ats": "greenhouse", "company": "coinbase",     "company_name": "Coinbase"},
    {"ats": "greenhouse", "company": "brex",         "company_name": "Brex"},
    {"ats": "greenhouse", "company": "chime",        "company_name": "Chime"},
    {"ats": "greenhouse", "company": "carta",        "company_name": "Carta"},
    {"ats": "greenhouse", "company": "robinhood",    "company_name": "Robinhood"},
    # Cloud / infra / dev tools
    {"ats": "greenhouse", "company": "gitlab",       "company_name": "GitLab"},
    {"ats": "greenhouse", "company": "databricks",   "company_name": "Databricks"},
    {"ats": "greenhouse", "company": "anthropic",    "company_name": "Anthropic"},
    {"ats": "greenhouse", "company": "postman",      "company_name": "Postman"},
    {"ats": "greenhouse", "company": "launchdarkly", "company_name": "LaunchDarkly"},
    {"ats": "greenhouse", "company": "temporal",     "company_name": "Temporal"},
    {"ats": "greenhouse", "company": "checkr",       "company_name": "Checkr"},
    {"ats": "greenhouse", "company": "verkada",      "company_name": "Verkada"},
    {"ats": "greenhouse", "company": "samsara",      "company_name": "Samsara"},
    # SaaS / productivity
    {"ats": "greenhouse", "company": "hubspot",      "company_name": "HubSpot"},
    {"ats": "greenhouse", "company": "asana",        "company_name": "Asana"},
    {"ats": "greenhouse", "company": "figma",        "company_name": "Figma"},
    {"ats": "greenhouse", "company": "discord",      "company_name": "Discord"},
    {"ats": "greenhouse", "company": "pinterest",    "company_name": "Pinterest"},
    {"ats": "greenhouse", "company": "duolingo",     "company_name": "Duolingo"},
    {"ats": "greenhouse", "company": "squarespace",  "company_name": "Squarespace"},
    {"ats": "greenhouse", "company": "mixpanel",     "company_name": "Mixpanel"},
    {"ats": "greenhouse", "company": "amplitude",    "company_name": "Amplitude"},
    {"ats": "greenhouse", "company": "lattice",      "company_name": "Lattice"},
    {"ats": "greenhouse", "company": "gusto",        "company_name": "Gusto"},
    # Consumer / marketplace
    {"ats": "greenhouse", "company": "airbnb",       "company_name": "Airbnb"},
    {"ats": "greenhouse", "company": "reddit",       "company_name": "Reddit"},
    {"ats": "greenhouse", "company": "lyft",         "company_name": "Lyft"},
    {"ats": "greenhouse", "company": "flexport",     "company_name": "Flexport"},

    # ── Lever (api.lever.co/v0/postings/{slug}) ──────────────────────────────
    {"ats": "lever", "company": "plaid",        "company_name": "Plaid"},
    {"ats": "lever", "company": "highspot",     "company_name": "Highspot"},

    # ── Ashby (api.ashbyhq.com/posting-api/job-board/{slug}) ─────────────────
    # All slugs verified 2026-02
    {"ats": "ashby", "company": "linear",       "company_name": "Linear"},
    {"ats": "ashby", "company": "clerk",        "company_name": "Clerk"},
    {"ats": "ashby", "company": "loom",         "company_name": "Loom"},
    {"ats": "ashby", "company": "retool",       "company_name": "Retool"},
    {"ats": "ashby", "company": "vercel",       "company_name": "Vercel"},
    {"ats": "ashby", "company": "supabase",     "company_name": "Supabase"},
    {"ats": "ashby", "company": "resend",       "company_name": "Resend"},
    {"ats": "ashby", "company": "neon",         "company_name": "Neon"},
    {"ats": "ashby", "company": "posthog",      "company_name": "PostHog"},
    {"ats": "ashby", "company": "watershed",    "company_name": "Watershed"},
    # AI / data companies on Ashby
    {"ats": "ashby", "company": "openai",       "company_name": "OpenAI"},
    {"ats": "ashby", "company": "cohere",       "company_name": "Cohere"},
    {"ats": "ashby", "company": "snyk",         "company_name": "Snyk"},
    {"ats": "ashby", "company": "sentry",       "company_name": "Sentry"},
    {"ats": "ashby", "company": "benchling",    "company_name": "Benchling"},
    {"ats": "ashby", "company": "zapier",       "company_name": "Zapier"},
    {"ats": "ashby", "company": "ramp",         "company_name": "Ramp"},
    {"ats": "ashby", "company": "deel",         "company_name": "Deel"},
    {"ats": "ashby", "company": "replit",       "company_name": "Replit"},

    # ── Workable (apply.workable.com/api/v3/accounts/{slug}/jobs) ────────────
    {"ats": "workable", "company": "typeform",      "company_name": "Typeform"},
    {"ats": "workable", "company": "hotjar",        "company_name": "Hotjar"},

    # ── Workday (POST /wday/cxs/{tenant}/{site}/jobs — CSRF via session warmup)
    # The scraper GETs the careers page first to capture the CALYPSO_CSRF_TOKEN
    # cookie, which is then sent as the X-Csrf-Token header on every POST.
    # All slugs below verified 2026-02.
    {
        "ats": "workday", "company": "salesforce",
        "company_name": "Salesforce",
        "wd_tenant": "salesforce", "wd_site": "External_Career_Site", "wd_instance": "wd12",
    },
    {
        "ats": "workday", "company": "adobe",
        "company_name": "Adobe",
        "wd_tenant": "adobe", "wd_site": "external_experienced", "wd_instance": "wd5",
    },
    {
        "ats": "workday", "company": "walmart",
        "company_name": "Walmart",
        "wd_tenant": "walmart", "wd_site": "WalmartExternal", "wd_instance": "wd5",
    },
    {
        "ats": "workday", "company": "paypal",
        "company_name": "PayPal",
        "wd_tenant": "paypal", "wd_site": "jobs", "wd_instance": "wd1",
    },
    # Cloudflare-protected (return HTTP 500 to non-browser clients):
    # microsoft (wd1/External_Microsoft_Careers_Portal), oracle (wd1/External),
    # cisco (wd5/*), apple (wd5/*), nike (wd1/*), target (wd12/External_Careers)

    # ── SmartRecruiters (api.smartrecruiters.com/v1/companies/{slug}/postings)
    # NOTE: SmartRecruiters now requires a company-specific smart_token for all
    # public API access — the public listings endpoint returns totalFound=0 for
    # every tested company.  Targets commented out until a workaround is found.
    # {"ats": "smartrecruiters", "company": "IKEA",       "company_name": "IKEA"},
    # {"ats": "smartrecruiters", "company": "HelloFresh",  "company_name": "HelloFresh"},

    # ── BambooHR (HTML careers page — {slug}.bamboohr.com/careers)
    # Note: BambooHR's careers pages are now JS-rendered (React SPA).
    # Only slugs where Playwright is available will successfully scrape content.
    # Listed here as targets for environments with Playwright installed.
    # {"ats": "bamboohr", "company": "udemy",       "company_name": "Udemy"},
    # {"ats": "bamboohr", "company": "procore",     "company_name": "Procore"},
    # {"ats": "bamboohr", "company": "headspace",   "company_name": "Headspace"},

    # ── iCIMS (HTML careers page — set careers_url to the search page)
    # iCIMS enterprise customers typically host careers on custom domains.
    # The {company}.icims.com/jobs/search URL pattern returns 404 for most
    # companies that have migrated to newer iCIMS hosting.
    # Add your own iCIMS targets here with the correct careers_url.
    # Example:
    # {"ats": "icims", "company": "mycompany", "company_name": "My Company",
    #  "careers_url": "https://careers.mycompany.com/jobs/search"},

    # ── Taleo (HTML careers page — set careers_url to the job search page)
    # Verified 2026-02: AT&T still on Taleo (12 US jobs).
    {
        "ats": "taleo", "company": "att",
        "company_name": "AT&T",
        "careers_url": "https://att.jobs/search-jobs",
    },
    {
        "ats": "taleo", "company": "baxter",
        "company_name": "Baxter International",
        "careers_url": "https://jobs.baxter.com/search-jobs",
    },

    # ── Aggregator APIs (single entry = many companies) ───────────────────────
    # The Muse — tech/data/product/design roles, all US companies
    {"ats": "themuse",        "company": "themuse-aggregator",        "company_name": "The Muse"},
    # Remotive — remote tech jobs; US-hinted locations kept
    {"ats": "remotive",       "company": "remotive-aggregator",       "company_name": "Remotive"},
    # RemoteOK — remote tech jobs; worldwide/US-hinted kept
    {"ats": "remoteok",       "company": "remoteok-aggregator",       "company_name": "RemoteOK"},
    # WeWorkRemotely — RSS feeds for programming/devops/product/design/data
    {"ats": "weworkremotely", "company": "weworkremotely-aggregator", "company_name": "WeWorkRemotely"},

    # ── API-key sources — auto-enabled when env vars are set ─────────────────
    # Each scraper checks env vars first; no key = graceful skip (no crash).
    #
    # USAJobs (data.usajobs.gov — free registration)
    #   Set USAJOBS_API_KEY + USAJOBS_EMAIL  →  https://developer.usajobs.gov/
    {"ats": "usajobs",  "company": "usajobs",  "company_name": "USAJobs"},
    #
    # Adzuna (api.adzuna.com — free developer plan, generous limits)
    #   Set ADZUNA_APP_ID + ADZUNA_APP_KEY    →  https://developer.adzuna.com/
    {"ats": "adzuna",   "company": "adzuna",   "company_name": "Adzuna"},
    #
    # Google Jobs via SerpAPI (serpapi.com — 100 free searches / month)
    #   Set SERPAPI_KEY                       →  https://serpapi.com/
    {"ats": "serpapi",  "company": "serpapi",  "company_name": "Google Jobs"},
    #
    # ── LinkedIn — public guest API (FREE, no key required) ──────────────────
    # Uses linkedin.com/jobs-guest/ endpoints — same HTML that non-logged-in
    # visitors see.  No token, no Apify, no cost.
    {"ats": "linkedin", "company": "software engineer", "company_name": "LinkedIn",
     "api_secret": '["data scientist", "product manager", "machine learning engineer", "devops engineer", "backend engineer", "frontend engineer", "software developer", "full stack developer"]'},
    #
    # ── Apify cloud actors ────────────────────────────────────────────────────
    # Free tier: $5 platform credits / month  →  https://apify.com/
    # Add APIFY_TOKEN as a GitHub repository secret to enable.
    # Run by the DAILY Apify workflow (scrape-jobs-apify.yml), not hourly.
    #
    # Indeed Jobs — valig/indeed-jobs-scraper (~$0.02/run at 200 results)
    {"ats": "apify", "company": "valig/indeed-jobs-scraper",
     "company_name": "Indeed (via Apify)",
     "api_secret": '{"keyword": "software engineer OR data scientist OR product manager OR machine learning engineer OR devops engineer OR backend developer OR frontend developer", "location": "United States", "maxItems": 200}'},
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
            "Supported ATS values: greenhouse, lever, workday, smartrecruiters, ashby,\n"
            "  bamboohr, workable, themuse, remotive, remoteok, weworkremotely,\n"
            "  usajobs, html, playwright"
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
        "--since-hours",
        metavar="N",
        type=int,
        default=None,
        help=(
            "Only include jobs posted within the last N hours.  "
            "Jobs with no posted_at date are always included.  "
            "Example: --since-hours 24"
        ),
    )
    parser.add_argument(
        "--only-ats",
        metavar="ATS[,ATS,...]",
        default=None,
        help=(
            "Comma-separated list of ATS names to run (all others skipped).  "
            "Example: --only-ats apify  or  --only-ats greenhouse,lever,ashby"
        ),
    )
    parser.add_argument(
        "--skip-ats",
        metavar="ATS[,ATS,...]",
        default=None,
        help=(
            "Comma-separated list of ATS names to skip.  "
            "Example: --skip-ats apify"
        ),
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

    if args.only_ats:
        allowed = {s.strip().lower() for s in args.only_ats.split(",")}
        targets = [t for t in targets if t.ats.lower() in allowed]
        log.info("--only-ats filter: keeping %d target(s) (%s)", len(targets), args.only_ats)
    elif args.skip_ats:
        skipped = {s.strip().lower() for s in args.skip_ats.split(",")}
        targets = [t for t in targets if t.ats.lower() not in skipped]
        log.info("--skip-ats filter: kept %d target(s) (skipped %s)", len(targets), args.skip_ats)
    log.info("Loaded %d scrape target(s)", len(targets))

    with JobScrapeOrchestrator() as orc:
        jobs = orc.run(targets, since_hours=args.since_hours)

    output_json = json.dumps(jobs, indent=2, ensure_ascii=False)

    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(output_json)
        log.info("Wrote %d jobs to %s", len(jobs), args.output)
    else:
        print(output_json)


if __name__ == "__main__":
    main()
