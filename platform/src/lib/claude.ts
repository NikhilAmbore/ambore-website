import Anthropic from '@anthropic-ai/sdk';
import type { AnalysisResult, InterviewQuestion } from '@/types';

const globalForAnthropic = globalThis as unknown as {
  anthropic: Anthropic | undefined;
};

function getAnthropic(): Anthropic {
  if (globalForAnthropic.anthropic) return globalForAnthropic.anthropic;
  const client = new Anthropic({ apiKey: process.env.ANTHROPIC_API_KEY ?? '' });
  if (process.env.NODE_ENV !== 'production') globalForAnthropic.anthropic = client;
  return client;
}

export async function claudeChat(
  system: string,
  user: string,
  maxTokens = 1024
): Promise<string> {
  const client = getAnthropic();
  const message = await client.messages.create({
    model: 'claude-sonnet-4-6',
    max_tokens: maxTokens,
    system,
    messages: [{ role: 'user', content: user }],
  });
  const block = message.content[0];
  return block.type === 'text' ? block.text : '';
}

export async function analyzeResume(
  resume: string,
  jobDescription: string
): Promise<AnalysisResult> {
  const text = await claudeChat(
    'You are an expert ATS analyst and career coach. Always respond with valid JSON only — no markdown, no explanation, just the JSON object.',
    `Analyze the following resume against the job description and return a comprehensive analysis.

RESUME:
${resume}

JOB DESCRIPTION:
${jobDescription}

Return this exact JSON structure:
{
  "score": <number 0-100, overall match score>,
  "atsScore": <number 0-100, ATS compatibility score>,
  "missingKeywords": [<important keywords from job description missing in resume>],
  "suggestions": [<5-8 specific, actionable improvement suggestions>],
  "improvedBullets": [<3-5 improved bullet points rewritten for impact and ATS keywords>],
  "skillGaps": [<skills/technologies in job description not in resume>],
  "weakSections": [<resume sections needing improvement, e.g. "Summary", "Skills">]
}

Scoring: score = keyword matches (40%) + experience relevance (30%) + skills alignment (20%) + presentation (10%). atsScore = formatting + keyword density + standard section headers + quantifiable achievements.`,
    2000
  );

  const result = JSON.parse(text) as AnalysisResult;
  result.score = Math.max(0, Math.min(100, result.score));
  result.atsScore = Math.max(0, Math.min(100, result.atsScore));
  return result;
}

export async function generateInterviewQuestions(
  jobTitle: string,
  level: string
): Promise<InterviewQuestion[]> {
  const text = await claudeChat(
    'You are an expert interviewer and career coach. Always respond with valid JSON only.',
    `Generate 10 interview questions for a ${level} ${jobTitle} position.

Return valid JSON only:
{
  "questions": [
    {
      "question": "<interview question>",
      "sampleAnswer": "<detailed STAR-method sample answer>",
      "tips": ["<tip 1>", "<tip 2>", "<tip 3>"]
    }
  ]
}

Include: behavioral (3-4), technical (3-4), situational (2-3). Make answers realistic and specific to the role level.`,
    3000
  );

  const result = JSON.parse(text) as { questions: InterviewQuestion[] };
  return result.questions;
}

export async function generateSummary(resumeText: string): Promise<string> {
  return claudeChat(
    'You are an expert resume writer. Write compelling, concise professional summaries.',
    `Write a 3-4 sentence professional summary based on this resume. Use active voice, be specific, and make it ATS-friendly. Return only the summary text.

RESUME:
${resumeText}`,
    300
  );
}
