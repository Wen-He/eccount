/*
 * counttorture.h: simple user-level performance/stress test of counters.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Copyright (c) 2017 Junchang Wang, NUPT.
 * Copyright (c) 2006 Paul E. McKenney, IBM.
 */

#include "api.h"

long duration_ms;
long writerstart;
int readerAffinity[16];
int writerAffinity[32];

#define R730_FREQ (1.7)    //FIXME: hack

uint64_t rdtsc_bare()
{
	uint64_t        time;
	uint32_t        msw, lsw;
	__asm__         __volatile__(
			"rdtsc\n\t"
			"mov %%edx, %0\n\t"
			"mov %%eax, %1\n\t"
			: "=r" (msw), "=r"(lsw)
			:   
			: "%rax","%rdx");
	time = ((uint64_t) msw << 32) | lsw;
	return time;
}

void wait_ticks(uint64_t ticks)
{
	uint64_t        current_time;
	uint64_t        time = rdtsc_bare();
	time += ticks;
	do {
		current_time = rdtsc_bare();
	} while (current_time < time);
}

/*
 * Test variables.
 */

atomic_t nthreadsrunning;
int nthreadsexpected;

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

int goflag __attribute__((__aligned__(CACHE_LINE_SIZE))) = GOFLAG_INIT;

#define COUNT_READ_RUN   10
#define COUNT_UPDATE_RUN 1000

#ifndef NEED_REGISTER_THREAD
#define count_register_thread(p)	do ; while (0)
#define count_unregister_thread(n)	do ; while (0)
#endif /* #ifndef NEED_REGISTER_THREAD */

#if defined(CHECK_CORRECTNESS)
#define CHECK_CORRECTNESS_LEN (1024*1024*2)
unsigned long global_chk_correct_seq = 0;
#endif

unsigned long garbage = 0; /* disable compiler optimizations. */

struct updater_thread_info {
	unsigned long start_c, stop_c;
	long number;
	long cpu;
	long cnt __attribute__((__aligned__(CACHE_LINE_SIZE)));
};

struct reader_thread_info {
	unsigned long start_c, stop_c;
	long number;
	long cpu;
	long cnt __attribute__((__aligned__(CACHE_LINE_SIZE)));
#if defined(CHECK_CORRECTNESS)
	unsigned long index;
	unsigned long tss[CHECK_CORRECTNESS_LEN];
	unsigned long results[CHECK_CORRECTNESS_LEN];
#endif
};

struct reader_thread_info readers_info[NR_THREADS];
struct updater_thread_info updaters_info[NR_THREADS];
int global_nwriters;
int global_nreaders;

/*
 * Performance test.
 */

void *count_read_perf_test(void *arg)
{
	int i;
	unsigned long j = 0;
	unsigned long __maybe_unused k = 0;
	struct reader_thread_info *th = (struct reader_thread_info*) arg;
	int me = th->cpu;
	long long n_reads_local = 0LL;

	printf("Reader thread runs on CPU %d \n", me);

	run_on(me);
	atomic_inc(&nthreadsrunning);
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 100);
	wait_ticks(100000 * me);
	th->start_c = rdtsc_bare();
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		for (i = COUNT_READ_RUN; i > 0; i--) {
#if defined(CHECK_CORRECTNESS)
			unsigned long ts = __sync_fetch_and_add(&global_chk_correct_seq, 1); 
#endif
			j = read_count(me);
#if defined(CHECK_CORRECTNESS)
			unsigned long index = readers_info[th->number].index;
			if (index < CHECK_CORRECTNESS_LEN) {
				readers_info[th->number].tss[index] = ts;
				readers_info[th->number].results[index] = j;
				WRITE_ONCE(readers_info[th->number].index, index+1);
			}
#endif

			barrier();
		}
		n_reads_local += COUNT_READ_RUN;
	}
	th->stop_c = rdtsc_bare();
	readers_info[th->number].cnt+= n_reads_local;
	garbage += j;

	return (NULL);
}

void *count_update_perf_test(void *arg)
{
	int i;
	unsigned long __maybe_unused k = 0;
	struct updater_thread_info *th = (struct updater_thread_info*) arg;
	int me = th->cpu;
	long long n_updates_local = 0LL;

	printf("Updater thread %ld runs on CPU %ld.\n", th->number, th->cpu);

	run_on(me);
	atomic_inc(&nthreadsrunning);
	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 10);
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		for (i = COUNT_UPDATE_RUN; i > 0; i--) {
			inc_count(th->number);
			barrier();
		}
		n_updates_local += COUNT_UPDATE_RUN;
	}
	updaters_info[th->number].cnt+= n_updates_local;

	return NULL;
}

void perftestinit(int nthreads)
{
	atomic_set(&nthreadsrunning, 0);
	nthreadsexpected = nthreads;
}

void perftestrun(int nthreads, int nreaders, int nupdaters)
{
	int i;
	long n_reads = 0L;
	long n_updates = 0L;

	smp_mb();
	while (atomic_read(&nthreadsrunning) < nthreads)
		poll(NULL, 0, 1);
	goflag = GOFLAG_RUN;
	smp_mb();
	poll(NULL, 0, duration_ms);
	smp_mb();
	goflag = GOFLAG_STOP;
	smp_mb();
	wait_all_threads();
	count_cleanup();
	for (i = 0; i < NR_THREADS; i++) {
		n_reads += readers_info[i].cnt;
		n_updates += updaters_info[i].cnt;
	}
	unsigned long reader_tsc = 0;
	for (i = 0; i < NR_THREADS; i++) {
		if (readers_info[i].start_c != 0) {
			printf("Reader %d takes %ld cycles to finish %ld read ops. (avg. %.f)\n",
					i, readers_info[i].stop_c-readers_info[i].start_c, readers_info[i].cnt,  (readers_info[i].stop_c-readers_info[i].start_c)/(double)readers_info[i].cnt);
			reader_tsc += readers_info[i].stop_c-readers_info[i].start_c;
		}
	}

#if defined(CHECK_CORRECTNESS)
	unsigned long j;
	FILE * fp = fopen("check_correctness.data", "w");
	if (fp == NULL) {
		printf("Error in creating check_correctness data log file.\n");
		return;
	}
	else {
		for (i = 0; i < 16; i++) {
			if (readers_info[i].index != 0) {
				for(j = 0; j < readers_info[i].index; j++) {
					//printf("%lu : %lu (%ld)\n", readers_info[i].tss[j], readers_info[i].results[j], readers_info[i].number);
					fprintf(fp, "th%ld %lu %lu\n", readers_info[i].number, readers_info[i].tss[j], readers_info[i].results[j]);
				}
			}
		}
	}
	fclose(fp);
#endif

	unsigned long final_count;
	final_count = final_read_count();
	if (n_updates != final_count) {
		printf("!!! Count mismatch(%d): %ld counted vs. %lu final value (final_read_count)\n",
				i, n_updates, final_count);
	}
	else
		printf("SUCCESS: Counting results verified!!!\n");

	printf("n_reads: %ld  n_updates: %ld  nreaders: %d  nupdaters: %d duration: %ld\n",
			n_reads, n_updates, nreaders, nupdaters, duration_ms);
	printf("ns/read: %g       ns/write: %g\n",
			(( reader_tsc / (double)n_reads)) / (double)R730_FREQ,
			((duration_ms * 1000*1000.*(double)nupdaters) / (double)n_updates));

	exit(0);
}

void pperftest(int nreaders, int nwriters)
{
	int i;

	global_nwriters = nwriters;
	global_nreaders = nreaders;

	perftestinit(nreaders + nwriters);
	for (i = 0; i < nreaders; i++) {
		readers_info[i].number = i;
		readers_info[i].cpu = readerAffinity[i];
		create_thread(count_read_perf_test, (void *)&readers_info[i]);
	}

	for (i = 0; i < nwriters; i++) {
		updaters_info[i].number = i;
		updaters_info[i].cpu = writerAffinity[i];
		create_thread(count_update_perf_test, (void *)&updaters_info[i]);
	}

	perftestrun(nreaders + nwriters, nreaders, nwriters);
}

/*
 * Mainprogram.
 */

void usage(int argc, char *argv[])
{
	fprintf(stderr, "Usage: %s pperf nreaders nwriters affinity_config_file duration (ms)\n", argv[0]);
	exit(-1);
}

int processAffinity(FILE * fp)
{
	int i;

	fprintf(stdout, "Affinity setting of readers: ");
	for (i = 0; i < 16; i++) {
		if (EOF == fscanf(fp, "%d", &readerAffinity[i]))
			return -1;
		fprintf(stdout, "%4d ", readerAffinity[i]);
	}
	fprintf(stdout, "\n");

	fprintf(stdout, "Affinity setting of writers: ");
	for (i = 0; i < 32; i++) {
		if (EOF == fscanf(fp, "%d", &writerAffinity[i]))
			return -1;
		fprintf(stdout, "%4d ", writerAffinity[i]);
	}
	fprintf(stdout, "\n");

	return 0;
}


int main(int argc, char *argv[])
{
	int nreaders = 1;
	int nwriters = 1;
	FILE * fp;

	smp_init();
	count_init();

	if (argc > 1) {
		if (strcmp(argv[1], "pperf") != 0) {
			fprintf(stdout, "We only support pperf.\n");
			usage(argc, argv);
			return -1;
		}
		else if (argc < 6) {
			fprintf(stdout, "Incorrect parameters.\n");
			usage(argc, argv);
			return -1;
		}      
		else {
			nreaders = strtoul(argv[2], NULL, 0);
			nwriters = strtoul(argv[3], NULL, 0);
			printf("affinity file: %s\n", argv[4]);
			fp = fopen(argv[4], "r");
			if (fp == NULL) {
				fprintf(stdout, "Incorrect affinity file parameter.\n");
				usage(argc, argv);
				return -1;
			}
			if (processAffinity(fp) != 0 ) {
				fprintf(stdout, "Incorrect affinity file format.\n");
				return -1;
			}

			duration_ms = strtoul(argv[5], NULL, 0);
			printf("==Test parameters: %d readers, %d writers,  duration(ms): %ld. ==\n", nreaders, nwriters, duration_ms);
			pperftest(nreaders, nwriters);
			fclose(fp);
		}
	}
	return 0;
}

/******************************/
/******** Backup code *********/
/******************************/

#if 0
/*
 * Correctness test.
 */

unsigned long flag_t1;
unsigned long t1_go;
unsigned long flag_t2;

void *thread_read_count1(void *arg)
{
	run_on(2);
	while (READ_ONCE(flag_t1) == 0) {
		;
	}
	WRITE_ONCE(t1_go, 1);
	smp_mb();
	*(unsigned long *)arg = read_count(0);
	return (NULL);
}

void *thread_read_count2(void *arg)
{
	run_on(4);
	while (READ_ONCE(flag_t2) == 0) {
		;
	}
	*(unsigned long *)arg = read_count(0);
	return (NULL);
}

void *count_correctness_test(void *arg)
{
	unsigned long j1 = 0;
	unsigned long j2 = 0;
	thread_id_t t1, t2;

	while (ACCESS_ONCE(goflag) == GOFLAG_INIT)
		poll(NULL, 0, 100);
	
	while (ACCESS_ONCE(goflag) == GOFLAG_RUN) {
		WRITE_ONCE(flag_t1, 0);
		WRITE_ONCE(t1_go, 0);
		WRITE_ONCE(flag_t2, 0);

		smp_mb();

		t1 = create_thread(thread_read_count1, (void *)&j1);
		t2 = create_thread(thread_read_count2, (void *)&j2);

		smp_mb();

		WRITE_ONCE(flag_t1, 1);
		smp_mb();
		while(READ_ONCE(t1_go) == 0) {
			;
		}
		WRITE_ONCE(flag_t2, 1);
		smp_mb();

		wait_thread(t1);
		wait_thread(t2);
		if (j1 > j2) {
			printf("=========out of order=========: %lu : %lu\n", j1, j2);
		}
	}

	return (NULL);
}
#endif
