-- Ambore Payment System — DB Migration v2
-- Adds: multi-plan support, anti-abuse columns, brute-force protection, canonical email dedup
-- Run in Railway PostgreSQL console BEFORE deploying.

-- ── Plan type (monthly | 3month | 6month | 1year) ────────────────────────────
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS subscription_plan TEXT DEFAULT 'free';

-- ── Canonical email (gmail dot/alias normalised) for dedup enforcement ────────
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS email_canonical TEXT;

-- Backfill canonical email for existing rows (simple lowercase, no gmail normalisation needed retroactively)
UPDATE "User" SET email_canonical = LOWER(email) WHERE email_canonical IS NULL;

-- Unique index — prevents same real inbox registering twice via dots/aliases
CREATE UNIQUE INDEX IF NOT EXISTS idx_user_email_canonical ON "User"(email_canonical);

-- ── Account suspension ────────────────────────────────────────────────────────
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS is_suspended     BOOLEAN  DEFAULT FALSE;
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS suspended_reason TEXT;

-- ── Brute-force login protection ──────────────────────────────────────────────
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS login_attempts     INTEGER    DEFAULT 0;
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS login_locked_until TIMESTAMPTZ;

-- ── IP tracking for signup abuse detection ────────────────────────────────────
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS signup_ip TEXT;

-- ── Indexes ───────────────────────────────────────────────────────────────────
CREATE INDEX IF NOT EXISTS idx_user_signup_ip        ON "User"(signup_ip);
CREATE INDEX IF NOT EXISTS idx_user_is_suspended     ON "User"(is_suspended);
CREATE INDEX IF NOT EXISTS idx_user_subscription_plan ON "User"(subscription_plan);
