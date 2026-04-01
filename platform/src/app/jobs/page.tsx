import { getServerSession } from 'next-auth';
import { redirect } from 'next/navigation';
import { authOptions } from '@/lib/auth';
import Sidebar from '@/components/layout/Sidebar';
import JobList from '@/components/jobs/JobList';

export const metadata = {
  title: 'Jobs | Ambore',
  description: 'Browse thousands of job listings and analyze them against your resume.',
};

export default async function JobsPage() {
  const session = await getServerSession(authOptions);
  if (!session?.user) redirect('/auth/signin?callbackUrl=/jobs');

  return (
    <div className="flex h-screen bg-[#09090B] overflow-hidden">
      <Sidebar />
      <main className="flex-1 overflow-y-auto">
        <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-6 pt-16 lg:pt-8">
          <div className="mb-6">
            <h1 className="text-xl sm:text-2xl font-bold text-[#F8FAFC]">Job Listings</h1>
            <p className="text-[#94A3B8] text-sm mt-1">
              Browse jobs and click &quot;Analyze&quot; to instantly check your resume match.
            </p>
          </div>
          <JobList />
        </div>
      </main>
    </div>
  );
}
