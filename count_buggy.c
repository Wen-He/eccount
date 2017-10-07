/*
 * count_buggy.c: Sample code to demonstrate miscounts in statistical counters
 *
 * Usage:  ./count_buggy pperf nreaders nwriters affinity_config_file duration (ms)
 * 		e.g.: ./count_buggy pperf 1 14 affinity.cross.conf 3000
 * Output: check_correctness.data in current directory
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

#define CHECK_CORRECTNESS

DEFINE_PER_THREAD(unsigned long, counter);

void inc_count(int me)
{
	__get_thread_var(counter)++;
}

unsigned long read_count(int me)
{
	int t;
	unsigned long sum = 0;

	for_each_thread(t)
		sum += per_thread(counter, t);

	return sum;
}

unsigned long final_read_count(void)
{
	return read_count(0);
}

void count_init(void)
{
}

void count_cleanup(void)
{
}

#include "counttorture_optimized.h"
