/**
 * Netlify Function: /api/chat
 * Proxies messages to Claude API so the API key never touches the browser.
 *
 * Set ANTHROPIC_API_KEY in Netlify → Site settings → Environment variables.
 */

const ANTHROPIC_API_KEY = process.env.ANTHROPIC_API_KEY;
const MODEL             = "claude-sonnet-4-6";
const MAX_TOKENS        = 512;

const SYSTEM_PROMPT = `You are Ambore AI, the friendly support assistant for the Ambore career platform.

Ambore is a completely FREE, all-in-one AI career platform with 7 tools — no credit card, no trial limits:

1. 💼 Job Portal — 7,000+ US tech jobs from 97 top companies (Stripe, OpenAI, Cloudflare, Databricks, Notion, Airbnb and more). Updated hourly from 10 sources: LinkedIn, Indeed, Greenhouse, Ashby, Workday, Remotive, WeWorkRemotely, RemoteOK, The Muse, USAJobs. Filter by work type, salary, date, and source.

2. 📄 AI Resume Builder — Paste any job description → get an ATS-optimised, tailored resume in seconds. 5 templates (Classic, Modern, Professional, Executive, Creative). Export to PDF or DOCX.

3. 📝 Cover Letter Generator — Upload resume + job description → polished, personalised cover letter. Download as TXT or PDF.

4. ✉️ Email Generator — Application emails, cold outreach, follow-ups, thank-you notes, and networking emails.

5. 💼 LinkedIn Optimizer — AI-generated headline, About section, skills list, and STAR-format experience bullets that attract recruiters.

6. 🌐 Portfolio Builder — Fill in your projects and experience → download a complete, beautiful portfolio website as a single HTML file. No coding needed.

7. 🎙 Interview AI Co-Pilot — Listens live during interviews and generates STAR-format answers in under 2 seconds. Covers 8 round types (HR screen, behavioural, technical, case, executive, etc.). Also analyses your screen for coding problems.

All data is stored in your browser (localStorage) — nothing is sent to external servers except AI API calls.
A free account is required to use the tools. Sign up takes under 10 seconds.

Rules:
- Keep answers concise and friendly (under 150 words unless the user asks for detail).
- If asked how to use a specific tool, give clear step-by-step guidance.
- If asked about pricing, always confirm: completely free, no credit card.
- If asked something unrelated to careers or Ambore, politely redirect.
- Never make up features that don't exist.
- Address the user as "you" and be warm and encouraging.`;

exports.handler = async (event) => {
  // CORS preflight
  if (event.httpMethod === "OPTIONS") {
    return {
      statusCode: 200,
      headers: corsHeaders(),
      body: "",
    };
  }

  if (event.httpMethod !== "POST") {
    return { statusCode: 405, headers: corsHeaders(), body: "Method Not Allowed" };
  }

  if (!ANTHROPIC_API_KEY) {
    return {
      statusCode: 500,
      headers: corsHeaders(),
      body: JSON.stringify({ error: "ANTHROPIC_API_KEY not configured in Netlify env vars." }),
    };
  }

  let body;
  try {
    body = JSON.parse(event.body);
  } catch {
    return { statusCode: 400, headers: corsHeaders(), body: JSON.stringify({ error: "Invalid JSON" }) };
  }

  const { message, history = [] } = body;

  if (!message || typeof message !== "string" || message.trim().length === 0) {
    return { statusCode: 400, headers: corsHeaders(), body: JSON.stringify({ error: "message is required" }) };
  }

  // Build messages array — keep last 10 turns to stay within token budget
  const messages = [
    ...history.slice(-10),
    { role: "user", content: message.trim() },
  ];

  try {
    const resp = await fetch("https://api.anthropic.com/v1/messages", {
      method: "POST",
      headers: {
        "Content-Type":      "application/json",
        "x-api-key":         ANTHROPIC_API_KEY,
        "anthropic-version": "2023-06-01",
      },
      body: JSON.stringify({
        model:      MODEL,
        max_tokens: MAX_TOKENS,
        system:     SYSTEM_PROMPT,
        messages,
      }),
    });

    if (!resp.ok) {
      const errText = await resp.text();
      console.error("Anthropic API error:", resp.status, errText);
      return {
        statusCode: 502,
        headers: corsHeaders(),
        body: JSON.stringify({ error: "AI service error. Please try again." }),
      };
    }

    const data = await resp.json();
    const reply = data.content?.[0]?.text ?? "Sorry, I didn't get a response. Please try again.";

    return {
      statusCode: 200,
      headers: { ...corsHeaders(), "Content-Type": "application/json" },
      body: JSON.stringify({ reply }),
    };
  } catch (err) {
    console.error("Function error:", err);
    return {
      statusCode: 500,
      headers: corsHeaders(),
      body: JSON.stringify({ error: "Something went wrong. Please try again." }),
    };
  }
};

function corsHeaders() {
  return {
    "Access-Control-Allow-Origin":  "*",
    "Access-Control-Allow-Headers": "Content-Type",
    "Access-Control-Allow-Methods": "POST, OPTIONS",
  };
}
