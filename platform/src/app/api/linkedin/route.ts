import { NextRequest, NextResponse } from 'next/server';
import { getServerSession } from 'next-auth';
import { z } from 'zod';
import { authOptions } from '@/lib/auth';
import { openai } from '@/lib/openai';
import prisma from '@/lib/prisma';

const schema = z.object({
  section: z.enum(['headline', 'summary', 'experience']),
  currentText: z.string().min(10).max(5000),
  targetRole: z.string().max(100).optional(),
  industry: z.string().max(100).optional(),
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

    const { section, currentText, targetRole, industry } = parsed.data;
    const userId = session.user.id;

    // Rate limit
    const today = new Date();
    today.setHours(0, 0, 0, 0);
    const count = await prisma.activityLog.count({
      where: { userId, type: 'linkedin_optimized', createdAt: { gte: today } },
    });
    if (count >= DAILY_LIMIT) {
      return NextResponse.json({ error: `Daily limit of ${DAILY_LIMIT} optimizations reached. Try again tomorrow.` }, { status: 429 });
    }

    const sectionPrompts = {
      headline: `Rewrite this LinkedIn headline to be more compelling and keyword-rich. Make it specific, not generic. Show value, not just title.
Current headline: "${currentText}"
${targetRole ? `Target role: ${targetRole}` : ''}
${industry ? `Industry: ${industry}` : ''}

Return 3 headline options (under 220 chars each), numbered 1-3. Then a brief tip on why they work.`,

      summary: `Rewrite this LinkedIn "About" section to be engaging, keyword-optimized, and showcase real value.
Current summary: "${currentText}"
${targetRole ? `Target role: ${targetRole}` : ''}

Rules:
- Start with a strong hook (not "I am a..." or "Experienced professional")
- Include specific metrics and achievements
- Use keywords naturally
- End with a clear call to action
- Keep it under 2,000 characters

Return the rewritten summary only.`,

      experience: `Improve these LinkedIn experience bullet points to be more impactful, metrics-driven, and ATS-friendly.
Current bullets: "${currentText}"
${targetRole ? `Target role: ${targetRole}` : ''}

For each bullet:
- Start with a strong action verb
- Add specific metrics where possible (%, $, time saved)
- Show impact, not just tasks
- Keep under 200 chars per bullet

Return the improved bullets in the same format.`,
    };

    const response = await openai.chat.completions.create({
      model: 'gpt-4o',
      messages: [
        {
          role: 'system',
          content: 'You are a LinkedIn optimization expert who has helped thousands of professionals land jobs at top companies. You know exactly what recruiters and ATS systems look for.',
        },
        {
          role: 'user',
          content: sectionPrompts[section],
        },
      ],
      temperature: 0.65,
      max_tokens: 700,
    });

    const optimized = response.choices[0]?.message?.content ?? '';

    await prisma.activityLog.create({
      data: {
        userId,
        type: 'linkedin_optimized',
        metadata: { section },
      },
    });

    return NextResponse.json({ success: true, optimized });
  } catch (error) {
    console.error('LinkedIn optimizer error:', error);
    return NextResponse.json({ error: 'Failed to optimize. Please try again.' }, { status: 500 });
  }
}
