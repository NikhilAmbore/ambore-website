export interface User {
  id: string;
  email: string;
  name?: string | null;
  image?: string | null;
  createdAt: Date;
  referralCode?: string | null;
  referredBy?: string | null;
}

export interface Resume {
  id: string;
  userId: string;
  title: string;
  content: string;
  fileUrl?: string | null;
  createdAt: Date;
  updatedAt: Date;
  analyses?: ResumeAnalysis[];
}

export interface ResumeAnalysis {
  id: string;
  resumeId: string;
  jobDescription: string;
  score: number;
  atsScore: number;
  missingKeywords: string[];
  suggestions: string[];
  improvedBullets: string;
  skillGaps: string[];
  weakSections: string[];
  createdAt: Date;
}

export interface Job {
  id: string;
  title: string;
  company: string;
  location: string;
  description: string;
  salary?: string | null;
  type: string;
  remote: boolean;
  url: string;
  postedAt: Date;
  tags: string[];
}

export interface SavedJob {
  userId: string;
  jobId: string;
  job?: Job;
}

export interface ActivityLog {
  id: string;
  userId: string;
  type: ActivityType;
  metadata?: Record<string, unknown> | null;
  createdAt: Date;
}

export type ActivityType =
  | 'resume_analyzed'
  | 'job_saved'
  | 'job_applied'
  | 'interview_practiced'
  | 'score_updated'
  | 'account_created'
  | 'cover_letter_generated'
  | 'linkedin_optimized';

export interface CareerScore {
  id: string;
  userId: string;
  overall: number;
  resumeScore: number;
  atsScore: number;
  interviewScore: number;
  updatedAt: Date;
}

export interface AnalysisResult {
  score: number;
  atsScore: number;
  missingKeywords: string[];
  suggestions: string[];
  improvedBullets: string[];
  skillGaps: string[];
  weakSections: string[];
}

export interface InterviewQuestion {
  question: string;
  sampleAnswer: string;
  tips: string[];
}

export interface DashboardData {
  careerScore: CareerScore | null;
  recentActivities: ActivityLog[];
  resumeCount: number;
  savedJobsCount: number;
}

export interface JobFilters {
  search?: string;
  type?: string;
  remote?: boolean;
  location?: string;
  salary?: string;
}

export interface NavItem {
  label: string;
  href: string;
  icon?: React.ComponentType<{ className?: string }>;
}

export interface PricingFeature {
  text: string;
  included: boolean;
}

export interface PricingPlan {
  name: string;
  price: string;
  period: string;
  description: string;
  features: string[];
  cta: string;
  highlighted: boolean;
  comingSoon?: boolean;
}

export interface Testimonial {
  id: string;
  name: string;
  role: string;
  company: string;
  quote: string;
  rating: number;
  initials: string;
  avatarColor: string;
}

export interface AnalysisStep {
  id: string;
  label: string;
  completed: boolean;
  active: boolean;
}

export interface ApiResponse<T = unknown> {
  success: boolean;
  data?: T;
  error?: string;
  message?: string;
}
