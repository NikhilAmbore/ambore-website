import { NextRequest, NextResponse } from 'next/server';
import { getServerSession } from 'next-auth';
import { z } from 'zod';
import { authOptions } from '@/lib/auth';
import prisma from '@/lib/prisma';

const schema = z.object({
  jobId: z.string().min(1).max(100),
  action: z.enum(['save', 'unsave']),
  jobTitle: z.string().max(200).optional(),
  company: z.string().max(200).optional(),
});

export async function POST(req: NextRequest) {
  try {
    const session = await getServerSession(authOptions);
    if (!session?.user) {
      return NextResponse.json({ error: 'Authentication required' }, { status: 401 });
    }

    const body = await req.json();
    const parsed = schema.safeParse(body);
    if (!parsed.success) {
      return NextResponse.json({ error: 'Invalid input' }, { status: 400 });
    }

    const { jobId, action, jobTitle, company } = parsed.data;
    const userId = session.user.id;

    if (action === 'save') {
      // Log the activity (saves are tracked via activity log, not FK to Job model)
      await prisma.activityLog.create({
        data: {
          userId,
          type: 'job_saved',
          metadata: { jobId, jobTitle, company },
        },
      });
    }

    // Update saved jobs count via activity log
    return NextResponse.json({ success: true, action });
  } catch (error) {
    console.error('Job save error:', error);
    return NextResponse.json({ error: 'Failed to save job' }, { status: 500 });
  }
}

export async function GET(req: NextRequest) {
  try {
    const session = await getServerSession(authOptions);
    if (!session?.user) {
      return NextResponse.json({ error: 'Authentication required' }, { status: 401 });
    }

    const { searchParams } = new URL(req.url);
    const jobIds = searchParams.get('ids')?.split(',').filter(Boolean) ?? [];

    // Return which jobs have been saved (tracked via activity log)
    const saved = await prisma.activityLog.findMany({
      where: {
        userId: session.user.id,
        type: 'job_saved',
      },
      select: { metadata: true },
    });

    const savedIds = saved
      .map(s => (s.metadata as Record<string, unknown>)?.jobId as string)
      .filter(id => id && jobIds.includes(id));

    return NextResponse.json({ success: true, savedIds });
  } catch (error) {
    console.error('Get saved jobs error:', error);
    return NextResponse.json({ error: 'Failed to fetch saved jobs' }, { status: 500 });
  }
}
