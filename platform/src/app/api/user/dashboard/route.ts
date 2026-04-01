import { NextRequest, NextResponse } from 'next/server';
import { getServerSession } from 'next-auth';
import { authOptions } from '@/lib/auth';
import prisma from '@/lib/prisma';

export async function GET(request: NextRequest) {
  try {
    const session = await getServerSession(authOptions);

    if (!session?.user) {
      return NextResponse.json({ error: 'Authentication required' }, { status: 401 });
    }

    const userId = session.user.id;

    const [careerScore, recentActivities, resumeCount, savedJobsCount] = await Promise.all([
      prisma.careerScore.findUnique({ where: { userId } }),
      prisma.activityLog.findMany({
        where: { userId },
        orderBy: { createdAt: 'desc' },
        take: 5,
      }),
      prisma.resume.count({ where: { userId } }),
      prisma.savedJob.count({ where: { userId } }),
    ]);

    return NextResponse.json({
      success: true,
      data: {
        careerScore,
        recentActivities,
        resumeCount,
        savedJobsCount,
      },
    });
  } catch (error) {
    console.error('Dashboard API error:', error);
    return NextResponse.json(
      { error: 'Failed to fetch dashboard data' },
      { status: 500 }
    );
  }
}
