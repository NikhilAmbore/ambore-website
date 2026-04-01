import { NextRequest, NextResponse } from 'next/server';
import { getServerSession } from 'next-auth';
import { z } from 'zod';
import { authOptions } from '@/lib/auth';
import { openai } from '@/lib/openai';
import prisma from '@/lib/prisma';

const schema = z.object({
  resumeText: z.string().min(50).max(20000),
  jobDescription: z.string().min(50).max(20000),
  tone: z.enum(['professional', 'enthusiastic', 'concise']).default('professional'),
});

const DAILY_LIMIT = 20;

export async function POST(req: NextRequest) {
  try {
    const session = await getServerSession(authOptions);
    if (!session?.user) {
      return NextResponse.json({ error: 'Authentication required' }, { status: 401 });
    }

    const body = await req.json();
    const parsed = schema.safeParse(body);
    if (!parsed.success) {
      return NextResponse.json({ error: parsed.error.errors[0]?.message ?? 'Invalid input' }, { status: 400 });
    }

    const { resumeText, jobDescription, tone } = parsed.data;
    const userId = session.user.id;

    // Rate limit
    const today = new Date();
    today.setHours(0, 0, 0, 0);
    const count = await prisma.activityLog.count({
      where: { userId, type: 'cover_letter_generated', createdAt: { gte: today } },
    });
    if (count >= DAILY_LIMIT) {
      return NextResponse.json({ error: `Daily limit of ${DAILY_LIMIT} cover letters reached. Try again tomorrow.` }, { status: 429 });
    }

    const toneInstructions = {
      professional: 'formal and professional tone, focused on achievements and qualifications',
      enthusiastic: 'enthusiastic and passionate tone showing genuine interest in the company',
      concise: 'brief and punchy — no more than 250 words, every sentence must add value',
    };

    const response = await openai.chat.completions.create({
      model: 'gpt-4o',
      messages: [
        {
          role: 'system',
          content: 'You are an expert cover letter writer. Write compelling, personalized cover letters that get responses. Never use generic phrases like "I am writing to apply". Be specific and concrete.',
        },
        {
          role: 'user',
          content: `Write a cover letter with a ${toneInstructions[tone]}.

RESUME:
${resumeText.slice(0, 8000)}

JOB DESCRIPTION:
${jobDescription.slice(0, 8000)}

Instructions:
- Open with a strong, specific hook — reference the company or role directly
- Show you understand what they are building / their mission
- Connect 2-3 specific achievements from the resume to the job requirements
- Keep it to 3-4 paragraphs
- End with a clear, confident call to action
- Do NOT use placeholder text like [Your Name] — write the full letter

Return only the cover letter text, no subject line, no "Dear Hiring Manager" boilerplate unless it fits naturally.`,
        },
      ],
      temperature: 0.7,
      max_tokens: 800,
    });

    const coverLetter = response.choices[0]?.message?.content ?? '';

    await prisma.activityLog.create({
      data: {
        userId,
        type: 'cover_letter_generated',
        metadata: { tone },
      },
    });

    return NextResponse.json({ success: true, coverLetter });
  } catch (error) {
    console.error('Cover letter error:', error);
    return NextResponse.json({ error: 'Failed to generate cover letter. Please try again.' }, { status: 500 });
  }
}
