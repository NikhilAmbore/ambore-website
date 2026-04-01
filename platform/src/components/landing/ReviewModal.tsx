'use client';

import { useState } from 'react';
import { X, Star } from 'lucide-react';
import toast from 'react-hot-toast';

interface ReviewModalProps {
  onClose: () => void;
  onSubmitted: () => void;
}

export default function ReviewModal({ onClose, onSubmitted }: ReviewModalProps) {
  const [rating, setRating] = useState(0);
  const [hovered, setHovered] = useState(0);
  const [comment, setComment] = useState('');
  const [name, setName] = useState('');
  const [role, setRole] = useState('');
  const [loading, setLoading] = useState(false);

  const submit = async () => {
    if (rating === 0) { toast.error('Please select a star rating'); return; }
    if (comment.trim().length < 10) { toast.error('Please write at least 10 characters'); return; }
    if (!name.trim()) { toast.error('Please enter your name'); return; }

    setLoading(true);
    try {
      const res = await fetch('/api/reviews', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ rating, comment: comment.trim(), name: name.trim(), role: role.trim() || undefined }),
      });
      const data = await res.json();
      if (!res.ok) throw new Error(data.error ?? 'Failed');
      toast.success('Review submitted! Thank you.');
      onSubmitted();
      onClose();
    } catch (err: unknown) {
      toast.error(err instanceof Error ? err.message : 'Failed to submit');
    } finally {
      setLoading(false);
    }
  };

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center p-4" onClick={onClose}>
      <div className="absolute inset-0 bg-black/70 backdrop-blur-sm" />
      <div
        className="relative w-full max-w-md bg-[#111113] border border-white/[0.1] rounded-2xl p-6 shadow-2xl"
        onClick={e => e.stopPropagation()}
      >
        <div className="flex items-center justify-between mb-5">
          <h2 className="text-lg font-bold text-[#F8FAFC]">Share your experience</h2>
          <button
            onClick={onClose}
            className="p-1.5 text-[#94A3B8] hover:text-white hover:bg-white/10 rounded-lg transition-colors"
          >
            <X className="w-4 h-4" />
          </button>
        </div>

        {/* Star rating */}
        <div className="mb-5">
          <label className="block text-sm font-medium text-[#CBD5E1] mb-2">Rating</label>
          <div className="flex gap-1">
            {[1, 2, 3, 4, 5].map(n => (
              <button
                key={n}
                onMouseEnter={() => setHovered(n)}
                onMouseLeave={() => setHovered(0)}
                onClick={() => setRating(n)}
                className="p-0.5 transition-transform hover:scale-110"
              >
                <Star
                  className="w-8 h-8 transition-colors"
                  fill={(hovered || rating) >= n ? '#F59E0B' : 'none'}
                  stroke={(hovered || rating) >= n ? '#F59E0B' : '#475569'}
                />
              </button>
            ))}
          </div>
          {(hovered || rating) > 0 && (
            <p className="text-xs text-[#94A3B8] mt-1">
              {['', 'Poor', 'Fair', 'Good', 'Very good', 'Excellent!'][hovered || rating]}
            </p>
          )}
        </div>

        {/* Name + Role */}
        <div className="grid grid-cols-2 gap-3 mb-4">
          <div>
            <label className="block text-xs font-medium text-[#94A3B8] mb-1.5">Your name *</label>
            <input
              value={name}
              onChange={e => setName(e.target.value)}
              placeholder="Jane Smith"
              className="w-full h-9 px-3 bg-white/[0.04] border border-white/10 rounded-lg text-sm text-[#F8FAFC] placeholder:text-[#475569] focus:outline-none focus:border-[#F97316] transition-colors"
            />
          </div>
          <div>
            <label className="block text-xs font-medium text-[#94A3B8] mb-1.5">Role (optional)</label>
            <input
              value={role}
              onChange={e => setRole(e.target.value)}
              placeholder="Software Engineer"
              className="w-full h-9 px-3 bg-white/[0.04] border border-white/10 rounded-lg text-sm text-[#F8FAFC] placeholder:text-[#475569] focus:outline-none focus:border-[#F97316] transition-colors"
            />
          </div>
        </div>

        {/* Comment */}
        <div className="mb-5">
          <label className="block text-xs font-medium text-[#94A3B8] mb-1.5">Your review *</label>
          <textarea
            value={comment}
            onChange={e => setComment(e.target.value)}
            rows={4}
            placeholder="How did Ambore help your job search? What did you love?"
            className="w-full bg-white/[0.04] border border-white/10 rounded-lg p-3 text-sm text-[#F8FAFC] placeholder:text-[#475569] resize-none focus:outline-none focus:border-[#F97316] transition-colors"
          />
          <p className="text-xs text-[#475569] mt-1">{comment.length} / 1000</p>
        </div>

        <button
          onClick={submit}
          disabled={loading}
          className="w-full h-11 bg-[#F97316] hover:bg-[#EA6D09] disabled:opacity-50 text-white font-semibold rounded-xl flex items-center justify-center gap-2 transition-all"
        >
          {loading ? (
            <><div className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" /> Submitting...</>
          ) : 'Submit Review'}
        </button>
      </div>
    </div>
  );
}
