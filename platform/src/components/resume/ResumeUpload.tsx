'use client';

import { useState, useCallback } from 'react';
import { useDropzone } from 'react-dropzone';
import { motion, AnimatePresence } from 'framer-motion';
import { Upload, FileText, X, Check, Loader2, Sparkles } from 'lucide-react';
import toast from 'react-hot-toast';
import { extractTextFromFile } from '@/lib/utils';
import type { AnalysisResult } from '@/types';

interface ResumeUploadProps {
  onAnalysisComplete: (result: AnalysisResult) => void;
  initialJobDescription?: string;
}

type ActiveTab = 'upload' | 'paste';
type AnalysisStep = 'idle' | 'parsing' | 'matching' | 'optimizing' | 'complete' | 'error';

const STEPS: { id: AnalysisStep; label: string }[] = [
  { id: 'parsing', label: 'Parsing resume' },
  { id: 'matching', label: 'Matching keywords' },
  { id: 'optimizing', label: 'Generating insights' },
  { id: 'complete', label: 'Complete' },
];

export default function ResumeUpload({ onAnalysisComplete, initialJobDescription = '' }: ResumeUploadProps) {
  const [tab, setTab] = useState<ActiveTab>('upload');
  const [resumeText, setResumeText] = useState('');
  const [jobDescription, setJobDescription] = useState(initialJobDescription);
  const [uploadedFile, setUploadedFile] = useState<File | null>(null);
  const [analysisStep, setAnalysisStep] = useState<AnalysisStep>('idle');
  const [errorMessage, setErrorMessage] = useState('');

  const currentStepIndex = STEPS.findIndex((s) => s.id === analysisStep);
  const isAnalyzing = analysisStep !== 'idle' && analysisStep !== 'complete' && analysisStep !== 'error';

  const onDrop = useCallback(async (acceptedFiles: File[]) => {
    const file = acceptedFiles[0];
    if (!file) return;

    setUploadedFile(file);
    try {
      const text = await extractTextFromFile(file);
      setResumeText(text);
      toast.success('Resume parsed successfully!');
    } catch (error) {
      toast.error('Failed to parse file. Please paste your resume text instead.');
      setTab('paste');
    }
  }, []);

  const { getRootProps, getInputProps, isDragActive } = useDropzone({
    onDrop,
    accept: {
      'application/pdf': ['.pdf'],
      'application/vnd.openxmlformats-officedocument.wordprocessingml.document': ['.docx'],
      'text/plain': ['.txt'],
    },
    maxFiles: 1,
    maxSize: 10 * 1024 * 1024, // 10MB
  });

  const handleAnalyze = async () => {
    if (!resumeText.trim() && !uploadedFile) {
      toast.error('Please upload or paste your resume first.');
      return;
    }
    if (!jobDescription.trim() || jobDescription.trim().length < 50) {
      toast.error('Please enter a job description (minimum 50 characters).');
      return;
    }

    setErrorMessage('');
    setAnalysisStep('parsing');

    try {
      const response = await fetch('/api/resume/analyze', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          resumeText: resumeText.trim(),
          jobDescription: jobDescription.trim(),
        }),
      });

      setAnalysisStep('matching');
      await new Promise((r) => setTimeout(r, 600));
      setAnalysisStep('optimizing');

      if (!response.ok) {
        const error = await response.json();
        throw new Error(error.error ?? 'Analysis failed. Please try again.');
      }

      const data = await response.json();
      setAnalysisStep('complete');

      setTimeout(() => {
        onAnalysisComplete(data.data);
      }, 400);
    } catch (error) {
      setAnalysisStep('error');
      const message = error instanceof Error ? error.message : 'Analysis failed. Please try again.';
      setErrorMessage(message);
      toast.error(message);
    }
  };

  return (
    <div className="bg-white/[0.04] border border-white/[0.08] rounded-xl p-6">
      <div className="flex items-center gap-2 mb-6">
        <Sparkles className="w-5 h-5 text-[#F97316]" />
        <h2 className="text-base font-semibold text-[#F8FAFC]">Resume Analyzer</h2>
      </div>

      <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
        {/* Left: Resume Input */}
        <div className="space-y-4">
          <div className="flex items-center gap-1 p-1 bg-white/[0.05] rounded-lg border border-white/[0.08] w-fit">
            {(['upload', 'paste'] as ActiveTab[]).map((t) => (
              <button
                key={t}
                onClick={() => setTab(t)}
                className={`px-4 py-1.5 rounded-md text-sm font-medium transition-all ${
                  tab === t
                    ? 'bg-[#F97316] text-white shadow-sm'
                    : 'text-[#94A3B8] hover:text-[#F8FAFC]'
                }`}
              >
                {t === 'upload' ? 'Upload File' : 'Paste Text'}
              </button>
            ))}
          </div>

          {tab === 'upload' ? (
            <div>
              {uploadedFile ? (
                <div className="flex items-center justify-between p-4 bg-[#22C55E]/10 border border-[#22C55E]/20 rounded-xl">
                  <div className="flex items-center gap-3">
                    <FileText className="w-5 h-5 text-[#22C55E]" />
                    <div>
                      <p className="text-sm font-medium text-[#F8FAFC] truncate max-w-[180px]">
                        {uploadedFile.name}
                      </p>
                      <p className="text-xs text-[#94A3B8]">
                        {(uploadedFile.size / 1024).toFixed(1)} KB · Ready to analyze
                      </p>
                    </div>
                  </div>
                  <button
                    onClick={() => { setUploadedFile(null); setResumeText(''); }}
                    className="p-1.5 text-[#94A3B8] hover:text-white hover:bg-white/10 rounded-lg transition-all"
                  >
                    <X className="w-4 h-4" />
                  </button>
                </div>
              ) : (
                <div
                  {...getRootProps()}
                  className={`relative border-2 border-dashed rounded-xl p-8 text-center cursor-pointer transition-all ${
                    isDragActive
                      ? 'border-[#F97316] bg-[#F97316]/5'
                      : 'border-white/15 hover:border-white/30 hover:bg-white/[0.02]'
                  }`}
                >
                  <input {...getInputProps()} />
                  <Upload className="w-8 h-8 text-[#94A3B8] mx-auto mb-3" />
                  <p className="text-sm font-medium text-[#CBD5E1] mb-1">
                    {isDragActive ? 'Drop your resume here' : 'Drop your resume here'}
                  </p>
                  <p className="text-xs text-[#94A3B8]">PDF, DOCX, or TXT · Max 10MB</p>
                  <button className="mt-4 h-8 px-4 bg-white/10 hover:bg-white/15 border border-white/10 rounded-lg text-xs text-[#CBD5E1] transition-all">
                    Browse Files
                  </button>
                </div>
              )}
            </div>
          ) : (
            <textarea
              value={resumeText}
              onChange={(e) => setResumeText(e.target.value)}
              placeholder="Paste your complete resume text here...&#10;&#10;John Doe&#10;john@email.com | LinkedIn: linkedin.com/in/johndoe&#10;&#10;EXPERIENCE&#10;Senior Engineer at Company XYZ (2021-Present)..."
              rows={12}
              className="w-full bg-white/[0.04] border border-white/10 rounded-xl p-4 text-sm text-[#F8FAFC] placeholder:text-[#475569] resize-none focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
            />
          )}
        </div>

        {/* Right: Job Description */}
        <div className="space-y-2">
          <label className="block text-sm font-medium text-[#CBD5E1]">
            Job Description <span className="text-[#EF4444]">*</span>
          </label>
          <textarea
            value={jobDescription}
            onChange={(e) => setJobDescription(e.target.value)}
            placeholder="Paste the full job description here...&#10;&#10;We're looking for a Senior Software Engineer with:&#10;• 5+ years of experience in React and TypeScript&#10;• Strong understanding of REST APIs&#10;• Experience with cloud platforms (AWS/GCP)..."
            rows={12}
            className="w-full bg-white/[0.04] border border-white/10 rounded-xl p-4 text-sm text-[#F8FAFC] placeholder:text-[#475569] resize-none focus:outline-none focus:border-[#F97316] focus:shadow-[0_0_0_3px_rgba(249,115,22,0.15)] transition-all"
          />
          <p className="text-xs text-[#94A3B8]">
            {jobDescription.length < 50
              ? `${50 - jobDescription.length} more characters needed`
              : `${jobDescription.length} characters — good!`}
          </p>
        </div>
      </div>

      {/* Error */}
      {analysisStep === 'error' && errorMessage && (
        <div className="mt-4 p-3 bg-[#EF4444]/10 border border-[#EF4444]/20 rounded-lg text-sm text-[#F87171]">
          {errorMessage}
        </div>
      )}

      {/* Progress Steps */}
      <AnimatePresence>
        {isAnalyzing && (
          <motion.div
            initial={{ opacity: 0, height: 0 }}
            animate={{ opacity: 1, height: 'auto' }}
            exit={{ opacity: 0, height: 0 }}
            className="mt-5 overflow-hidden"
          >
            <div className="flex items-center gap-2 flex-wrap">
              {STEPS.map((s, i) => {
                const isCompleted = i < currentStepIndex;
                const isActive = s.id === analysisStep;
                return (
                  <div key={s.id} className="flex items-center gap-2">
                    <div
                      className={`flex items-center gap-1.5 px-3 py-1 rounded-full text-xs font-medium transition-all ${
                        isCompleted
                          ? 'bg-[#22C55E]/15 text-[#4ADE80] border border-[#22C55E]/20'
                          : isActive
                          ? 'bg-[#F97316]/15 text-[#FB923C] border border-[#F97316]/20'
                          : 'bg-white/5 text-[#94A3B8] border border-white/10'
                      }`}
                    >
                      {isCompleted ? (
                        <Check className="w-3 h-3" />
                      ) : isActive ? (
                        <Loader2 className="w-3 h-3 animate-spin" />
                      ) : (
                        <div className="w-3 h-3 rounded-full border border-current opacity-40" />
                      )}
                      {s.label}
                    </div>
                    {i < STEPS.length - 1 && <div className="w-4 h-px bg-white/10" />}
                  </div>
                );
              })}
            </div>
          </motion.div>
        )}
      </AnimatePresence>

      {/* Analyze Button */}
      <div className="mt-6 flex justify-end">
        <button
          onClick={handleAnalyze}
          disabled={isAnalyzing}
          className="inline-flex items-center gap-2.5 h-11 px-7 bg-[#F97316] hover:bg-[#EA6D09] disabled:opacity-50 disabled:cursor-not-allowed text-white font-semibold rounded-lg text-sm transition-all shadow-[0_0_20px_rgba(249,115,22,0.3)] hover:shadow-[0_0_30px_rgba(249,115,22,0.5)]"
        >
          {isAnalyzing ? (
            <>
              <Loader2 className="w-4 h-4 animate-spin" />
              Analyzing...
            </>
          ) : (
            <>
              <Sparkles className="w-4 h-4" />
              Analyze Resume
            </>
          )}
        </button>
      </div>
    </div>
  );
}
