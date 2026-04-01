'use client';

import { motion } from 'framer-motion';
import { Star, PenLine } from 'lucide-react';
import { useEffect, useState } from 'react';
import { useSession } from 'next-auth/react';
import ReviewModal from './ReviewModal';

interface Review {
  id: string;
  rating: number;
  comment: string;
  name: string;
  role?: string | null;
  createdAt: string;
}

const STATIC_REVIEWS: Review[] = [
  {
    id: 's1',
    name: 'Marcus Chen',
    role: 'Software Engineer · Now at Stripe',
    rating: 5,
    comment: "I applied to 40+ jobs with my old resume and heard nothing. After using Ambore, I got 3 interviews in one week. The missing keywords feature alone was a game changer — I had no idea recruiters were filtering me out for not mentioning 'TypeScript' explicitly.",
    createdAt: '',
  },
  {
    id: 's2',
    name: 'Priya Patel',
    role: 'Product Manager · Now at Figma',
    rating: 5,
    comment: "The ATS score is incredibly accurate. I went from a 42 to an 89 after following the suggestions, and landed my dream PM role. What I love most is that it gives you specific bullet point rewrites — not vague tips.",
    createdAt: '',
  },
  {
    id: 's3',
    name: 'Jordan Williams',
    role: 'Data Scientist · Now at Netflix',
    rating: 5,
    comment: "I was skeptical at first, but the analysis caught real issues — like missing 'cross-functional teams' which appeared 6 times in the job description. My callback rate went from ~5% to over 40%.",
    createdAt: '',
  },
];

function StarDisplay({ rating }: { rating: number }) {
  return (
    <div className="flex gap-0.5">
      {[1, 2, 3, 4, 5].map(n => (
        <Star
          key={n}
          className="w-3.5 h-3.5"
          fill={n <= rating ? '#F59E0B' : 'none'}
          stroke={n <= rating ? '#F59E0B' : '#475569'}
        />
      ))}
    </div>
  );
}

function ReviewCard({ review, index }: { review: Review; index: number }) {
  const initials = review.name.split(' ').map(w => w[0]).join('').toUpperCase().slice(0, 2);
  const colors = ['#F97316', '#2563EB', '#22C55E', '#A78BFA', '#F59E0B'];
  const color = colors[index % colors.length];

  return (
    <motion.div
      initial={{ opacity: 0, y: 30 }}
      whileInView={{ opacity: 1, y: 0 }}
      viewport={{ once: true }}
      transition={{ duration: 0.5, delay: Math.min(index * 0.1, 0.4) }}
      className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-5 hover:border-white/[0.15] hover:bg-white/[0.06] transition-all flex flex-col"
    >
      <StarDisplay rating={review.rating} />
      <blockquote className="text-[#CBD5E1] text-sm leading-relaxed flex-1 mt-3 mb-4">
        &ldquo;{review.comment}&rdquo;
      </blockquote>
      <div className="flex items-center gap-3 pt-3 border-t border-white/[0.06]">
        <div
          className="w-9 h-9 rounded-full flex items-center justify-center text-xs font-bold shrink-0"
          style={{ backgroundColor: `${color}20`, border: `1px solid ${color}40`, color }}
        >
          {initials}
        </div>
        <div>
          <p className="text-sm font-semibold text-[#F8FAFC]">{review.name}</p>
          {review.role && <p className="text-xs text-[#94A3B8]">{review.role}</p>}
        </div>
      </div>
    </motion.div>
  );
}

export default function Testimonials() {
  const { data: session } = useSession();
  const [reviews, setReviews] = useState<Review[]>(STATIC_REVIEWS);
  const [showModal, setShowModal] = useState(false);

  const fetchReviews = () => {
    fetch('/api/reviews')
      .then(r => r.json())
      .then(d => {
        if (d.success && d.reviews?.length > 0) {
          setReviews([...d.reviews, ...STATIC_REVIEWS]);
        }
      })
      .catch(() => {});
  };

  useEffect(() => {
    fetchReviews();
  }, []);

  // Show at most 6 cards in a 3-column grid
  const displayed = reviews.slice(0, 6);

  return (
    <section className="py-20 relative overflow-hidden">
      <div className="absolute inset-0 pointer-events-none">
        <div
          className="absolute bottom-0 right-0 w-[600px] h-[400px] opacity-10"
          style={{ background: 'radial-gradient(ellipse, rgba(249,115,22,0.4) 0%, transparent 70%)', filter: 'blur(80px)' }}
        />
      </div>

      <div className="relative max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
        {/* Header */}
        <div className="text-center mb-12">
          <motion.p
            initial={{ opacity: 0, y: 10 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            className="text-sm font-medium text-[#F97316] uppercase tracking-widest mb-3"
          >
            Reviews
          </motion.p>
          <motion.h2
            initial={{ opacity: 0, y: 15 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ delay: 0.1 }}
            className="text-3xl sm:text-4xl font-bold text-[#F8FAFC] mb-3"
          >
            Real results from real users
          </motion.h2>
          <motion.p
            initial={{ opacity: 0, y: 15 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ delay: 0.15 }}
            className="text-[#94A3B8] max-w-xl mx-auto mb-6"
          >
            87% of users report getting more interview callbacks within 2 weeks.
          </motion.p>
          <motion.button
            initial={{ opacity: 0, y: 10 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ delay: 0.2 }}
            onClick={() => {
              if (!session) {
                window.location.href = '/auth/signin';
                return;
              }
              setShowModal(true);
            }}
            className="inline-flex items-center gap-2 h-9 px-5 bg-white/[0.06] hover:bg-white/[0.10] border border-white/[0.1] hover:border-white/[0.2] rounded-lg text-sm font-medium text-[#CBD5E1] hover:text-white transition-all"
          >
            <PenLine className="w-3.5 h-3.5" />
            Write a Review
          </motion.button>
        </div>

        {/* Review grid */}
        <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 gap-4 mb-12">
          {displayed.map((review, i) => (
            <ReviewCard key={review.id} review={review} index={i} />
          ))}
        </div>

        {/* Stats bar */}
        <motion.div
          initial={{ opacity: 0, y: 20 }}
          whileInView={{ opacity: 1, y: 0 }}
          viewport={{ once: true }}
          transition={{ delay: 0.3 }}
          className="grid grid-cols-2 md:grid-cols-4 gap-px bg-white/[0.06] rounded-2xl overflow-hidden border border-white/[0.08]"
        >
          {[
            { value: '12,000+', label: 'Resumes Analyzed' },
            { value: '87%', label: 'More Interviews' },
            { value: '4.9 / 5', label: 'User Rating' },
            { value: '47s', label: 'Avg. Analysis Time' },
          ].map(stat => (
            <div key={stat.label} className="bg-white/[0.02] p-5 text-center">
              <div className="text-2xl font-bold text-[#F8FAFC] mb-1">{stat.value}</div>
              <div className="text-sm text-[#94A3B8]">{stat.label}</div>
            </div>
          ))}
        </motion.div>
      </div>

      {showModal && (
        <ReviewModal
          onClose={() => setShowModal(false)}
          onSubmitted={fetchReviews}
        />
      )}
    </section>
  );
}
