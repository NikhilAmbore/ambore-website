import { NextRequest, NextResponse } from 'next/server';
import { getServerSession } from 'next-auth';
import { z } from 'zod';
import { authOptions } from '@/lib/auth';
import { claudeChat } from '@/lib/claude';
import prisma from '@/lib/prisma';

const schema = z.object({
  question: z.string().min(5).max(500),
  role: z.string().max(100).optional(),
  company: z.string().max(100).optional(),
  context: z.string().max(2000).optional(),
});

const DAILY_LIMIT = 30;

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

    const { question, role, company, context } = parsed.data;
    const userId = session.user.id;

    const today = new Date();
    today.setHours(0, 0, 0, 0);
    const count = await prisma.activityLog.count({
      where: { userId, type: 'interview_practiced', createdAt: { gte: today } },
    });
    if (count >= DAILY_LIMIT) {
      return NextResponse.json({ error: `Daily limit of ${DAILY_LIMIT} practice answers reached. Try again tomorrow.` }, { status: 429 });
    }

    const systemCtx = role || company
      ? `The candidate is interviewing for a ${role ?? 'software engineering'} role${company ? ` at ${company}` : ''}.`
      : 'The candidate is preparing for a general tech interview.';

    const answer = await claudeChat(
      `You are an expert interview coach. ${systemCtx} Generate a strong STAR-method answer that is specific, quantified, and compelling. Sound natural — not like a robot reciting a template.`,
      `Interview question: "${question}"${context ? `\n\nBackground context: ${context}` : ''}

Generate a complete STAR answer. Include:
- Specific numbers/metrics in the Result section
- Concrete technical or business details
- A natural, conversational tone
- 2-3 sentences per section

Format as:
**Situation:** ...
**Task:** ...
**Action:** ...
**Result:** ...

Then add one line: **Key takeaway:** (what this shows about you as a candidate)`,
      600
    );

    await prisma.activityLog.create({
      data: {
        userId,
        type: 'interview_practiced',
        metadata: { question: question.slice(0, 100), role, company },
      },
    });

    try {
      const existing = await prisma.careerScore.findUnique({ where: { userId } });
      if (existing) {
        const newScore = Math.min(100, existing.interviewScore + 2);
        await prisma.careerScore.update({
          where: { userId },
          data: {
            interviewScore: newScore,
            overall: Math.round((existing.resumeScore + existing.atsScore + newScore) / 3),
          },
        });
      } else {
        await prisma.careerScore.create({
          data: { userId, interviewScore: 10, resumeScore: 0, atsScore: 0, overall: 3 },
        });
      }
    } catch (scoreErr) {
      console.error('Career score update failed (non-fatal):', scoreErr);
    }

    return NextResponse.json({ success: true, answer });
  } catch (error) {
    console.error('Interview API error:', error);
    return NextResponse.json({ error: 'Failed to generate answer. Please try again.' }, { status: 500 });
  }
}
