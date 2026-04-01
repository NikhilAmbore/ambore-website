'use client';

import { motion } from 'framer-motion';
import { Upload, ClipboardList, Sparkles } from 'lucide-react';

const steps = [
  {
    number: '01',
    icon: Upload,
    title: 'Upload Your Resume',
    description:
      'Upload your resume as PDF, DOCX, or paste the text directly. We support all common resume formats and extract text automatically.',
    color: '#F97316',
    bgColor: 'rgba(249, 115, 22, 0.1)',
    borderColor: 'rgba(249, 115, 22, 0.2)',
  },
  {
    number: '02',
    icon: ClipboardList,
    title: 'Paste Job Description',
    description:
      'Copy any job posting from LinkedIn, Indeed, or any company career page and paste it in. Our AI analyzes every requirement and keyword.',
    color: '#2563EB',
    bgColor: 'rgba(37, 99, 235, 0.1)',
    borderColor: 'rgba(37, 99, 235, 0.2)',
  },
  {
    number: '03',
    icon: Sparkles,
    title: 'Get Optimized Resume',
    description:
      'Receive your ATS score, missing keywords, specific improvement suggestions, and rewritten bullet points tailored to the job — in seconds.',
    color: '#22C55E',
    bgColor: 'rgba(34, 197, 94, 0.1)',
    borderColor: 'rgba(34, 197, 94, 0.2)',
  },
];

export default function HowItWorks() {
  return (
    <section className="py-24 relative">
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
        {/* Header */}
        <div className="text-center mb-16">
          <motion.p
            initial={{ opacity: 0, y: 10 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ duration: 0.5 }}
            className="text-sm font-medium text-[#F97316] uppercase tracking-widest mb-3"
          >
            How it works
          </motion.p>
          <motion.h2
            initial={{ opacity: 0, y: 15 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ duration: 0.5, delay: 0.1 }}
            className="text-3xl sm:text-4xl font-bold text-[#F8FAFC] mb-4"
          >
            Three steps to your dream job
          </motion.h2>
          <motion.p
            initial={{ opacity: 0, y: 15 }}
            whileInView={{ opacity: 1, y: 0 }}
            viewport={{ once: true }}
            transition={{ duration: 0.5, delay: 0.2 }}
            className="text-[#94A3B8] text-lg max-w-xl mx-auto"
          >
            No complexity, no lengthy onboarding. Just results.
          </motion.p>
        </div>

        {/* Steps */}
        <div className="relative">
          {/* Connector line (desktop) */}
          <div className="hidden lg:block absolute top-20 left-[calc(16.67%+2rem)] right-[calc(16.67%+2rem)] h-px bg-gradient-to-r from-[#F97316]/30 via-[#2563EB]/30 to-[#22C55E]/30" />

          <div className="grid grid-cols-1 lg:grid-cols-3 gap-8 lg:gap-12">
            {steps.map((step, index) => {
              const Icon = step.icon;
              return (
                <motion.div
                  key={index}
                  initial={{ opacity: 0, y: 30 }}
                  whileInView={{ opacity: 1, y: 0 }}
                  viewport={{ once: true }}
                  transition={{ duration: 0.6, delay: index * 0.15 }}
                  className="relative flex flex-col items-center text-center"
                >
                  {/* Number + Icon */}
                  <div className="relative mb-6">
                    {/* Step number badge */}
                    <div className="absolute -top-2 -right-2 w-6 h-6 rounded-full bg-[#09090B] border border-white/10 flex items-center justify-center z-10">
                      <span className="text-xs font-bold text-[#94A3B8]">{step.number}</span>
                    </div>
                    {/* Icon circle */}
                    <div
                      className="w-16 h-16 rounded-2xl flex items-center justify-center"
                      style={{
                        background: step.bgColor,
                        border: `1px solid ${step.borderColor}`,
                        boxShadow: `0 0 30px ${step.bgColor}`,
                      }}
                    >
                      <Icon className="w-7 h-7" style={{ color: step.color }} />
                    </div>
                  </div>

                  {/* Content */}
                  <h3 className="text-xl font-semibold text-[#F8FAFC] mb-3">{step.title}</h3>
                  <p className="text-[#94A3B8] text-sm leading-relaxed max-w-xs mx-auto">
                    {step.description}
                  </p>

                  {/* Mobile connector */}
                  {index < steps.length - 1 && (
                    <div className="lg:hidden w-px h-8 mt-8 bg-gradient-to-b from-white/10 to-transparent" />
                  )}
                </motion.div>
              );
            })}
          </div>
        </div>

        {/* Bottom CTA */}
        <motion.div
          initial={{ opacity: 0, y: 20 }}
          whileInView={{ opacity: 1, y: 0 }}
          viewport={{ once: true }}
          transition={{ duration: 0.5, delay: 0.4 }}
          className="mt-16 text-center"
        >
          <p className="text-[#94A3B8] text-sm mb-4">
            Average time from upload to optimized resume
          </p>
          <div className="inline-flex items-center gap-2 px-4 py-2 bg-[#22C55E]/10 border border-[#22C55E]/20 rounded-full">
            <span className="text-2xl font-bold text-[#22C55E]">47</span>
            <span className="text-[#22C55E] font-medium">seconds</span>
          </div>
        </motion.div>
      </div>
    </section>
  );
}
