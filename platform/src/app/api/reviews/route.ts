import { NextRequest, NextResponse } from 'next/server';
import { getServerSession } from 'next-auth';
import { z } from 'zod';
import { authOptions } from '@/lib/auth';
import prisma from '@/lib/prisma';

const schema = z.object({
  rating: z.number().int().min(1).max(5),
  comment: z.string().min(10).max(1000).trim(),
  name: z.string().min(1).max(100).trim(),
  role: z.string().max(100).trim().optional(),
});

export async function GET() {
  try {
    const reviews = await prisma.review.findMany({
      orderBy: { createdAt: 'desc' },
      take: 20,
      select: {
        id: true,
        rating: true,
        comment: true,
        name: true,
        role: true,
        createdAt: true,
      },
    });
    return NextResponse.json({ success: true, reviews });
  } catch (error) {
    console.error('Get reviews error:', error);
    return NextResponse.json({ error: 'Failed to fetch reviews' }, { status: 500 });
  }
}

export async function POST(req: NextRequest) {
  try {
    const session = await getServerSession(authOptions);
    if (!session?.user) {
      return NextResponse.json({ error: 'Sign in to leave a review' }, { status: 401 });
    }

    const body = await req.json();
    const parsed = schema.safeParse(body);
    if (!parsed.success) {
      return NextResponse.json({ error: 'Invalid input', details: parsed.error.flatten() }, { status: 400 });
    }

    const { rating, comment, name, role } = parsed.data;
    const userId = session.user.id;

    // One review per user — upsert pattern
    const existing = await prisma.review.findFirst({ where: { userId } });
    let review;
    if (existing) {
      review = await prisma.review.update({
        where: { id: existing.id },
        data: { rating, comment, name, role: role ?? null },
      });
    } else {
      review = await prisma.review.create({
        data: { userId, rating, comment, name, role: role ?? null },
      });
    }

    return NextResponse.json({ success: true, review });
  } catch (error) {
    console.error('Submit review error:', error);
    return NextResponse.json({ error: 'Failed to submit review' }, { status: 500 });
  }
}
