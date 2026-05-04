-- Ambore Payment System — DB Migration (Dodo Payments)
-- Run this in the Railway PostgreSQL console BEFORE deploying.

ALTER TABLE "User" ADD COLUMN IF NOT EXISTS ai_calls_total               INTEGER      DEFAULT 0;
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS dodo_customer_id             TEXT;
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS dodo_subscription_id         TEXT;
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS subscription_status          TEXT         DEFAULT 'free';
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS subscription_current_period_end TIMESTAMPTZ;
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS monthly_ai_calls             INTEGER      DEFAULT 0;
ALTER TABLE "User" ADD COLUMN IF NOT EXISTS monthly_reset_at             TIMESTAMPTZ;

CREATE INDEX IF NOT EXISTS idx_user_dodo_customer ON "User"(dodo_customer_id);
