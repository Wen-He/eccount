/*
 * count_buggy.pml: To demonstrate the counting bug in traditional statistical
 * counter algorithms.  Source code and documentation can be found at
 * https://github.com/junchangwang.
 * 
 * Usage:
 *    make && ./count_buggy && spin -t -p count_buggy.pml
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
 * Copyright (c) 2018 Junchang Wang, NUPT.
 */
#define N_WRITER 2
#define N_READER 2

int counters[N_WRITER]
int sum[N_READER]
byte stop_flag

proctype writer(byte id)
{
	do
	:: ( stop_flag != 1 ) ->
		/* We regard increment operation as atomic to save state space. */
		counters[id] = counters[id] + 1;
	:: else -> break;
	od
}

proctype reader(byte id)
{
	sum[id] = counters[0];
	sum[id] = sum[id] + counters[1];
}

init 
{ 
	atomic { run writer(0); run writer(1); }

	byte n;
	n = _nr_pr;
	skip;
	run reader(0);
	run reader(1);
	(n == _nr_pr); /* To make sure the two reader requests have finished. */

	stop_flag = 1;

	assert(sum[0] <= sum[1]);
}
