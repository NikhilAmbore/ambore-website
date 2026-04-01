import { NextRequest, NextResponse } from 'next/server';
import { getServerSession } from 'next-auth';
import { z } from 'zod';
import { authOptions } from '@/lib/auth';
import prisma from '@/lib/prisma';
import { analyzeResume } from '@/lib/claude';

const analyzeSchema = z.object({
  resumeText: z.string().min(10, 'Resume text is too short').max(50000, 'Resume text is too long'),
  jobDescription: z
    .string()
    .min(50, 'Job description must be at least 50 characters')
    .max(20000, 'Job description is too long'),
  resumeId: z.string().optional(),
});

export async function POST(request: NextRequest) {
  try {
    const session = await getServerSession(authOptions);
    if (!session?.user) {
      return NextResponse.json({ error: 'Authentication required' }, { status: 401 });
    }

    const userId = session.user.id;
    const body = await request.json();

    const validation = analyzeSchema.safeParse(body);
    if (!validation.success) {
      return NextResponse.json(
        { error: validation.error.errors[0]?.message ?? 'Invalid input' },
        { status: 400 }
      );
    }

    const { resumeText, jobDescription, resumeId } = validation.data;

    // Rate limit: 10 analyses per user per day
    const today = new Date();
    today.setHours(0, 0, 0, 0);
    const todayCount = await prisma.activityLog.count({
      where: { userId, type: 'resume_analyzed', createdAt: { gte: today } },
    });
    if (todayCount >= 10) {
      return NextResponse.json(
        { error: 'Daily analysis limit reached (10 per day). Please try again tomorrow.' },
        { status: 429 }
      );
    }

    // Run AI analysis
    const analysisResult = await analyzeResume(resumeText, jobDescription);

    // Save or find resume record
    let resume;
    if (resumeId) {
      resume = await prisma.resume.findFirst({ where: { id: resumeId, userId } });
    }
    if (!resume) {
      const titlePreview = resumeText.slice(0, 50).split('\n')[0] ?? 'My Resume';
      resume = await prisma.resume.create({
        data: { userId, title: titlePreview, content: resumeText },
      });
    }

    // Save analysis
    const savedAnalysis = await prisma.resumeAnalysis.create({
      data: {
        resumeId: resume.id,
        jobDescription,
        score: analysisResult.score,
        atsScore: analysisResult.atsScore,
        missingKeywords: analysisResult.missingKeywords,
        suggestions: analysisResult.suggestions,
        improvedBullets: JSON.stringify(analysisResult.improvedBullets ?? []),
        skillGaps: analysisResult.skillGaps,
        weakSections: analysisResult.weakSections,
      },
    });

    // Log activity
    await prisma.activityLog.create({
      data: {
        userId,
        type: 'resume_analyzed',
        metadata: {
          resumeId: resume.id,
          score: analysisResult.score,
          atsScore: analysisResult.atsScore,
          jobDescription: jobDescription.slice(0, 100),
        },
      },
    });

    // Update career score
    try {
      const existingScore = await prisma.careerScore.findUnique({ where: { userId } });
      const newResumeScore = analysisResult.score;
      const newAtsScore = analysisResult.atsScore;
      const overall = Math.round((newResumeScore + newAtsScore) / 2);

      if (existingScore) {
        await prisma.careerScore.update({
          where: { userId },
          data: {
            resumeScore: Math.max(existingScore.resumeScore, newResumeScore),
            atsScore: Math.max(existingScore.atsScore, newAtsScore),
            overall: Math.max(existingScore.overall, overall),
          },
        });
      } else {
        await prisma.careerScore.create({
          data: { userId, resumeScore: newResumeScore, atsScore: newAtsScore, overall, interviewScore: 0 },
        });
      }
    } catch (scoreErr) {
      console.error('Career score update failed (non-fatal):', scoreErr);
    }

    // Parse improvedBullets safely
    let improvedBullets: string[] = [];
    if (Array.isArray(analysisResult.improvedBullets)) {
      improvedBullets = analysisResult.improvedBullets;
    } else {
      try {
        improvedBullets = JSON.parse(savedAnalysis.improvedBullets || '[]');
      } catch {
        improvedBullets = [];
      }
    }

    return NextResponse.json({
      success: true,
      data: { ...analysisResult, improvedBullets, analysisId: savedAnalysis.id },
    });
  } catch (error) {
    console.error('Resume analysis error:', error);

    if (error instanceof Error && error.message.includes('API key')) {
      return NextResponse.json(
        { error: 'AI service configuration error. Please contact support.' },
        { status: 500 }
      );
    }

    return NextResponse.json({ error: 'Analysis failed. Please try again.' }, { status: 500 });
  }
}
