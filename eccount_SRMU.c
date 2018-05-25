/*
 * eccount_SRMU: Single-reader-multi-updater version of ECCount. Complete 
 * code and documentation can be found at https://github.com/junchangwang.
 * Test result analysis can be found in Section 5.3 and 5.4 of ECCount paper.
 * 
 * api.h and count_stat.c own to Paul's excellent work at
 * http://kernel.org/pub/linux/kernel/people/paulmck/perfbook/perfbook.html.
 *
 * Usage: ./eccount_SRMU pperf nreaders nwriters affinity_config_file duration (ms)
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
 */

#include "api.h"

extern int global_nwriters; // Defined in counttorture_optimized.h

struct counter{
	long v __attribute__((__aligned__(CACHE_LINE_SIZE)));
};

struct counter counterA[NR_THREADS] __attribute__((__aligned__(CACHE_LINE_SIZE)));
struct counter counterB[NR_THREADS] __attribute__((__aligned__(CACHE_LINE_SIZE)));

int ABflag;
unsigned long older_snapshot;

void inc_count(long thread_num)
{
	if ( READ_ONCE(ABflag) ) {
		WRITE_ONCE(counterA[thread_num].v, READ_ONCE(counterA[thread_num].v) + 1);
	}
	else {
		WRITE_ONCE(counterB[thread_num].v, READ_ONCE(counterB[thread_num].v) + 1);
	}
}

unsigned long read_count(int me)
{
	int i;
	unsigned long sum = 0;
	unsigned long temp = 0;

	// Complement ABflag
	if (READ_ONCE(ABflag))
		WRITE_ONCE(ABflag, 0);
	else
		WRITE_ONCE(ABflag, 1);

	for (i = 0; i < global_nwriters; i++) {
		if ( ! READ_ONCE(ABflag) ) {
			sum += READ_ONCE(counterA[i].v);
		}
		else {
			sum += READ_ONCE(counterB[i].v);
		}
	}
	temp = sum;
	sum += older_snapshot;
	older_snapshot = temp;
	return sum; 
}

unsigned long final_read_count(void)
{
	unsigned long sum = 0;

	sum = read_count(0);
	return sum;
}

void count_init(void)
{
	ABflag = 1;
}

void count_cleanup(void)
{
}

#include "counttorture_optimized.h"
