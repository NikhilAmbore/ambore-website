import OpenAI from 'openai';
import { AnalysisResult, InterviewQuestion } from '@/types';

const globalForOpenAI = globalThis as unknown as {
  openai: OpenAI | undefined;
};

function getOpenAI(): OpenAI {
  if (globalForOpenAI.openai) return globalForOpenAI.openai;
  const client = new OpenAI({ apiKey: process.env.OPENAI_API_KEY ?? '' });
  if (process.env.NODE_ENV !== 'production') globalForOpenAI.openai = client;
  return client;
}

export const openai = new Proxy({} as OpenAI, {
  get(_target, prop) {
    return getOpenAI()[prop as keyof OpenAI];
  },
});

export async function analyzeResume(
  resume: string,
  jobDescription: string
): Promise<AnalysisResult> {
  const prompt = `You are an expert ATS (Applicant Tracking System) analyst and career coach with 15+ years of experience. Analyze the following resume against the job description and provide a comprehensive analysis.

RESUME:
${resume}

JOB DESCRIPTION:
${jobDescription}

Analyze the match between the resume and job description. Provide your response as valid JSON only, with no additional text or markdown formatting.

Return this exact JSON structure:
{
  "score": <number 0-100, overall match score>,
  "atsScore": <number 0-100, ATS compatibility score>,
  "missingKeywords": [<array of important keywords/skills from job description missing in resume>],
  "suggestions": [<array of 5-8 specific, actionable improvement suggestions>],
  "improvedBullets": [<array of 3-5 improved bullet points rewritten for impact and keywords>],
  "skillGaps": [<array of skills/technologies mentioned in job description not in resume>],
  "weakSections": [<array of resume sections that need improvement, e.g., "Summary", "Work Experience", "Skills">]
}

Scoring criteria:
- score: Weight keyword matches (40%), experience relevance (30%), skills alignment (20%), overall presentation (10%)
- atsScore: Focus on formatting, keyword density, standard section headers, quantifiable achievements

Be specific and actionable in suggestions. Improved bullets should demonstrate the STAR method with quantifiable results.`;

  const response = await openai.chat.completions.create({
    model: 'gpt-4o',
    messages: [
      {
        role: 'system',
        content:
          'You are an expert ATS analyst and career coach. Always respond with valid JSON only.',
      },
      { role: 'user', content: prompt },
    ],
    temperature: 0.3,
    max_tokens: 2000,
    response_format: { type: 'json_object' },
  });

  const content = response.choices[0]?.message?.content;
  if (!content) {
    throw new Error('No response from OpenAI');
  }

  const result = JSON.parse(content) as AnalysisResult;

  result.score = Math.max(0, Math.min(100, result.score));
  result.atsScore = Math.max(0, Math.min(100, result.atsScore));

  return result;
}

export async function generateInterviewQuestions(
  jobTitle: string,
  level: string
): Promise<InterviewQuestion[]> {
  const prompt = `Generate 10 interview questions for a ${level} ${jobTitle} position.

Return valid JSON only with this structure:
{
  "questions": [
    {
      "question": "<interview question>",
      "sampleAnswer": "<detailed sample answer using STAR method>",
      "tips": ["<tip 1>", "<tip 2>", "<tip 3>"]
    }
  ]
}

Include a mix of: behavioral (3-4 questions), technical (3-4 questions), situational (2-3 questions).
Make answers realistic, detailed, and specific to the role level.`;

  const response = await openai.chat.completions.create({
    model: 'gpt-4o',
    messages: [
      {
        role: 'system',
        content: 'You are an expert interviewer and career coach. Always respond with valid JSON only.',
      },
      { role: 'user', content: prompt },
    ],
    temperature: 0.7,
    max_tokens: 3000,
    response_format: { type: 'json_object' },
  });

  const content = response.choices[0]?.message?.content;
  if (!content) {
    throw new Error('No response from OpenAI');
  }

  const result = JSON.parse(content) as { questions: InterviewQuestion[] };
  return result.questions;
}

export async function generateSummary(resumeText: string): Promise<string> {
  const prompt = `Based on the following resume, write a compelling professional summary in 3-4 sentences.
The summary should highlight the candidate's most impressive achievements, skills, and career focus.
Use active voice, be specific, and make it ATS-friendly.

RESUME:
${resumeText}

Return only the summary text, no JSON wrapper needed.`;

  const response = await openai.chat.completions.create({
    model: 'gpt-4o',
    messages: [
      {
        role: 'system',
        content:
          'You are an expert resume writer. Write compelling, concise professional summaries.',
      },
      { role: 'user', content: prompt },
    ],
    temperature: 0.6,
    max_tokens: 300,
  });

  return response.choices[0]?.message?.content ?? '';
}

export default openai;
