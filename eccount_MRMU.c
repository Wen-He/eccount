/*
 * eccount_MRMU: Multi-reader-multi-updater version of ECCount. Complete 
 * code and documentation can be found at https://github.com/junchangwang.
 * 
 * api.h and count_stat.c own to Paul's excellent work at
 * http://kernel.org/pub/linux/kernel/people/paulmck/perfbook/perfbook.html.
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

#include <limits.h>
#include "eccount_MRMU.h"
#include "eccount_slab.h"

extern int global_nwriters;
extern int global_nreaders;

struct snapshot * global_updating_snapshot;
struct snapshot * global_old_snapshots;

unsigned long global_timestamp = 0;
unsigned long global_sum = 0;
unsigned long global_cleaner_flag;
int cleaner_exit;

void inc_count(long thread_num)
{
	struct snapshot * sp = READ_ONCE(global_updating_snapshot);
	sp->counters[thread_num].v ++;
}

unsigned long sumup(struct snapshot * sp)
{
    unsigned long sum = 0;

    for (int i = 0; i < global_nwriters; i++) {
		sum += sp->counters[i].v;
    }
    return sum;
}

unsigned long sumup_floatings(struct snapshot * sp, unsigned long timestamp, unsigned long * list_len)
{
	int i;
    unsigned long sum = 0;

    if (sp == NULL)
        return 0;

    for (i = 0; sp != NULL; i++, sp = READ_ONCE(sp->next)) {
        if (sp->timestamp > timestamp)
            continue;
        else {
            sum += sumup(sp);
        }
    }

    if (list_len)
        *list_len = i;

    return sum;
}

int cleanup_old_snapshots(struct snapshot * sp)
{
	int steps_head_anchor = 0;
	int steps_head_rep = 0;
	struct snapshot * rep;
	struct snapshot * repp;
	struct snapshot * rep_anchor;

	rep = READ_ONCE(sp);
	if ( (rep->anchor == 1) || (rep->next == NULL))
		return -1;

	repp = READ_ONCE(rep->next);
	if ( (repp->anchor == 1) || (repp->next == NULL))
		return -1;

	rep_anchor = READ_ONCE(repp->next);
	if ( (rep_anchor->anchor == 1) || (rep_anchor->next == NULL))
		return -1;

	// Search snapshot anchor
	while (READ_ONCE(rep_anchor->next) != NULL) {
		while (rep_anchor->timestamp != (rep_anchor->next->timestamp + 1)) {
			rep = rep_anchor;
			repp = READ_ONCE(rep_anchor->next);
			steps_head_rep = steps_head_anchor;
			printf("ERROR: missing timestamp %lu : %ld\n", rep_anchor->timestamp, rep_anchor->next->timestamp);
			poll(NULL, 0, 1);
		}
		rep_anchor = READ_ONCE(rep_anchor->next);
		steps_head_anchor ++;
	}

	// Double check
	if (rep_anchor->anchor != 1) {
        printf("ERROR in cleanup floatings (anchor not found).\n");
        return -1;
    }

	// To make sure the list is long enough before cleaning up
	if (steps_head_anchor < 200)
		return -1;

	if (steps_head_rep <= 100) {
		for (int i = 0; (i < (100 - steps_head_rep)) && (repp != NULL); i++) {
			rep = repp;
			repp = READ_ONCE(repp->next);
		}
		steps_head_rep = 100;
	}

	struct snapshot * repp_t = repp;

	// To make sure no pending updaters
	struct counter * counters_t;
	counters_t = (struct counter *)calloc(NR_THREADS, sizeof(struct counter));
    if (counters_t == NULL) {
        printf("Error in cleanup_old_snapshots (malloc).\n");
        return -1;
    }
	for (struct snapshot * spt = READ_ONCE(sp); spt != repp; spt = READ_ONCE(spt->next)) {
		for (int i = 0; i < global_nwriters; i++)
			counters_t[i].v += spt->counters[i].v;
	}
	for (int i = 0; i < global_nwriters; i++) {
		if (counters_t[i].v == 0) {
			//printf("Pending updaters found. Giving up cleanup job.\n");
			free(counters_t);
			return -1;
		}
	}
	free(counters_t);

	// Reduce the size of old snapshots by replacing snapshots in between *repp and *rep_anchor with a new snapshot
	// The replacement process is similar to RCU to avoid removing snapshots accessing by readers.
	struct snapshot * new_anchor = eccount_snapshot_malloc();
    if (new_anchor == NULL)
    {
        printf("Error in cleanup_old_snapshots (malloc).\n");
        return -1;
    }
	new_anchor->anchor = 1;
	new_anchor->reader_leaved = 1;
	new_anchor->timestamp = READ_ONCE(repp->timestamp);
	new_anchor->next = NULL;
	for (struct snapshot * spt = repp; spt != NULL; spt = spt->next) {
		for (int i = 0; i < global_nwriters; i++) {
			new_anchor->counters[i].v += spt->counters[i].v;
		}
	}

	// Replace snapshots between *repp and *rep_anchor by a new snapshot by utilizing a RCU-like strategy.
	if (__sync_bool_compare_and_swap(&rep->next, repp_t, new_anchor)) {

		if (rep->timestamp != new_anchor->timestamp + 1)
			printf("ERROR: bad timestamp after inserting new anchor.\n");

		smp_mb();

		// Now the new snapshot has been linked to rep->next.
		// Wait until all previous readers have left.
		unsigned long timestamp_t = READ_ONCE(global_timestamp);
		for (struct snapshot * spt = READ_ONCE(global_old_snapshots); spt != NULL; spt = spt->next) {
			while ( (spt->timestamp < timestamp_t) && (READ_ONCE(spt->reader_leaved) != 1) ) 
				poll(NULL, 0, 1);
		}

		//printf("To free old snapshots. %d - %d\n", steps_head_anchor, steps_head_rep);

		//Cleanup job
		int t = 0;
		for (struct snapshot * spt = repp; spt != NULL; spt = repp) {
			repp = READ_ONCE(repp->next);
			eccount_snapshot_free(spt);
			t ++;
		}

		return 0;
	}
	else
	{
		eccount_snapshot_free(new_anchor);
		return -1;
	}
}

void * cleanup_thread(void * arg)
{
	int rst;

	printf("===Cleanup thread starts.\n");
	while(1) {
		if (READ_ONCE(cleaner_exit) == 1)
			pthread_exit(NULL);

		rst = cleanup_old_snapshots(READ_ONCE(global_old_snapshots));
		if (rst == -1) 
			poll(NULL, 0, 1);
	}
}

unsigned long read_count(int me)
{
    unsigned long sum = 0;
    struct snapshot * new_snapshot; 
	struct snapshot * new_snapshot_old_value;
    struct snapshot * latest_snapshot;
	struct snapshot * latest_snapshot_old_value;

    new_snapshot = eccount_snapshot_malloc();
    if (new_snapshot == NULL)
    {
        printf("Error in read_count (malloc).\n");
        return 0;
    }

	new_snapshot->timestamp = __sync_fetch_and_add(&global_timestamp, 1);
    do {
		smp_mb();
		new_snapshot_old_value = READ_ONCE(global_updating_snapshot);
    } while ( ! __sync_bool_compare_and_swap(&global_updating_snapshot, new_snapshot_old_value, new_snapshot));

	latest_snapshot = new_snapshot_old_value;

restart:
	smp_mb();
	struct snapshot * global_old_snapshots_t = READ_ONCE(global_old_snapshots);
	latest_snapshot_old_value = global_old_snapshots_t;

    if ( latest_snapshot_old_value->timestamp < latest_snapshot->timestamp ) {
        WRITE_ONCE(latest_snapshot->next, latest_snapshot_old_value);
        if (! __sync_bool_compare_and_swap(&global_old_snapshots, latest_snapshot_old_value, latest_snapshot))
            goto restart;
    }
    else if ( latest_snapshot_old_value->timestamp > latest_snapshot->timestamp ) {
        // This is the corner case. We first search the right position and 
		// then insert the latest snapshot to build an inorder linked list
        struct snapshot * rep = latest_snapshot_old_value;
        struct snapshot * repp = READ_ONCE(latest_snapshot_old_value->next);

        while ( repp->timestamp > latest_snapshot->timestamp ) {
			rep = repp;
			repp = READ_ONCE(repp->next);
        }

		latest_snapshot_old_value = repp;
		WRITE_ONCE(latest_snapshot->next, latest_snapshot_old_value);

        if ( ! __sync_bool_compare_and_swap(&rep->next, latest_snapshot_old_value, latest_snapshot))
            goto restart;

#if 0
		unsigned long dd = 0;
		for (int tt = 0; tt < global_nwriters; tt++)
			dd += latest_snapshot->counters[tt].v;
		printf("Inserting out-of-order snapshot: %lu in between %lu:%lu. Thread: %d. Missing data: %lu\n", 
				latest_snapshot->timestamp, rep->timestamp, repp->timestamp, me, dd);
#endif
    }
    else {
        printf("!!!Error in inserting snapshot into floating list (Duplicated timestamp values) %lu:%lu.\n",
				latest_snapshot_old_value->timestamp, latest_snapshot->timestamp);
        return 0;
    }

	smp_mb();
	unsigned long garbage;
    sum += sumup_floatings(global_old_snapshots_t, new_snapshot->timestamp, &garbage);

	// The reader has finished all its job.
	// Marking reader_leaved to inform the system that this thread has left
	// and won't touch the linked list anymore (such that, e.g., latest_snapshot can be safely freed).
	smp_mb();
	WRITE_ONCE(latest_snapshot->reader_leaved, 1);

    return sum;
}

unsigned long final_read_count(void)
{
    unsigned long sum = 0;
    unsigned long list_len = 0;

    sum += sumup_floatings(READ_ONCE(global_old_snapshots), ULONG_MAX, &list_len);
    sum += sumup(READ_ONCE(global_updating_snapshot));
    printf("final read count. List lenght: %ld\n", list_len);

    return sum;
}

void count_init(void)
{
	pthread_t tid;

    WRITE_ONCE(global_cleaner_flag, 0UL);

	struct snapshot * sp = eccount_snapshot_malloc();
    if (sp == NULL)
    {
        printf("Error in count_init (malloc).\n");
		exit(-1);
    }
	sp->anchor = 1;
	sp->reader_leaved = 1;
	sp->timestamp = __sync_fetch_and_add(&global_timestamp, 1);
	WRITE_ONCE(global_old_snapshots, sp);
	
	WRITE_ONCE(global_updating_snapshot, eccount_snapshot_malloc());
    if (global_updating_snapshot == NULL)
    {
        printf("Error in count_init (malloc).\n");
		exit(-1);
    }
	WRITE_ONCE(global_updating_snapshot->timestamp, __sync_fetch_and_add(&global_timestamp, 1));

	WRITE_ONCE(cleaner_exit, 0);
	if (pthread_create(&tid, NULL, cleanup_thread, NULL) != 0) {
		perror("create cleanup thread.\n");
		exit(-1);
	}
}

void count_cleanup(void)
{
	WRITE_ONCE(cleaner_exit, 1);
}

#include "counttorture_optimized.h"

