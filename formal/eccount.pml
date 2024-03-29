/*
 * eccount.pml: The formal verification of ECCount algorithm, which is
 * presented in Section 3.4 of ECCount paper. Source code and documentation
 * of ECCount can be found at https://github.com/junchangwang.
 * 
 * Usage:
 *   - For server with handreds of gigabytes of memory:
 *       make && ./eccount
 *   - For server with a few gigabytes of memory:
 *       spin -a eccount.pml && gcc -O2 -DBITSTATE -o eccount pan.c && ./eccount
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
#define N_SNAPSHOT 4

typedef snapshot {
	short timestamp;
	bool allocated;
	short next;
	int counters[N_WRITER]
}
snapshot snapshots[N_SNAPSHOT];

/* To record the information of reader processes. */
typedef reader_info {
	byte id;
	byte timestamp; 
	int sum;
}
reader_info readers[N_READER];

/* Global variables */
byte g_timestamp;  /* Global shared timestamp */
short g_updating_snapshot;  /* Indicating counter array which updaters are incrementing */
short g_old_snapshots;  /* indicatting old shapshots list */
byte stop_flag;


/**********************************************************/
/*********** Linked list to record old snapshots **********/
/**********************************************************/

/* Users need to define variable *allocated_snapshot_id* before using this helper function. */
inline snapshot_malloc( )
{
	byte snapshot_ptr = 0;
	/* To simplify the verification, we assume the snapshot allocate
	 * function is atomic. In real C code, a lock-free allocator should be
	 * used. */
	atomic {
	do
	:: (snapshot_ptr >= N_SNAPSHOT) -> 
		allocated_snapshot_id = -1; /* Error happens */
		break;
	:: else ->
		if
		:: ( !(snapshots[snapshot_ptr].allocated) ) ->
			snapshots[snapshot_ptr].allocated = 1;
			allocated_snapshot_id = snapshot_ptr;
			goto L1_mal;
		:: else -> 
			snapshot_ptr = snapshot_ptr + 1;
		fi
	od
L1_mal:	skip;
	} /* end of atomic */
}

inline snapshot_free(index)
{
	atomic {
	snapshots[index].timestamp = 0;
	snapshots[index].allocated = 0;
	snapshots[index].next = 0;
	snapshots[index].counters[0] = 0;
	snapshots[index].counters[1] = 0;
	} /* end of atomic */
}

/* Users need to define variable *sum* before using this helper function. *
 * No primitive *atomic* in this function because we want to verify interleaving
 * between concurrent read and write operations.                                  */
inline sumup_list(tsp)
{
	short ptr = g_old_snapshots;
	do
	:: ptr >= N_SNAPSHOT -> break;
	:: ptr == -1 -> break;
	:: else ->
		if
		:: (snapshots[ptr].timestamp > tsp) -> 
			/* Skip snapshots with larger timestamp values, which
			 * are generated by subsequent read requests. */
			ptr = snapshots[ptr].next;
		:: else ->
			sum = sum + snapshots[ptr].counters[0];
			sum = sum + snapshots[ptr].counters[1];
			ptr = snapshots[ptr].next;
		fi
	od
}

/*****************************************/
/***********  ECCount algorithm **********/
/*****************************************/

proctype writer(byte id)
{
	do
	:: stop_flag -> break;
	:: else ->
		snapshots[g_updating_snapshot].counters[id] ++; 
		skip;
	od
}

proctype reader(byte id)
{
	byte allocated_snapshot_id = 0;
	/* Atomically allocate a new snapshot */
	atomic {
		snapshot_malloc( );
		if
		:: (allocated_snapshot_id == -1) -> 
			printf("Error in allocating snapshot.\n");
		:: else ->
			printf("\nSuccessfully allocated a new snapshot.\n");
		fi
	}

	byte tmp;
	/* Increment timestamp value atomically.  The primitive *atomic* in
	 * Promela is equivalent to the primitive FAA in real C code.      */
	atomic { 
		tmp = g_updating_snapshot; 
		snapshots[tmp].timestamp = g_timestamp; 
		g_timestamp ++; 
	}

	/* Swap the snapshots indicated by g_updating_snapshot and
	 * allocated_snapshot_id, and then insert the latest snapshot into
	 * global linked list. The primitive *atomic* in Promela is equivalent
	 * to the primitive SWAP in real C code.                            */
	atomic {
		g_updating_snapshot = allocated_snapshot_id;
		snapshots[tmp].next = g_old_snapshots;
		g_old_snapshots = tmp;
	}

	int sum;
	/* Sum up snapshots whose timestamp values are less than or equal to
	 * the timestamp value of this read request. */
	/* No primitive *atomic* wrapping this function because we want to verify
	 * interleaving between concurrent read and write operations. */
	sumup_list(snapshots[tmp].timestamp);

	/* Fill in reader request info, which will be used in printting out summary. */
	atomic {
		readers[id].id = id;
		readers[id].sum = sum;
		readers[id].timestamp = snapshots[tmp].timestamp;
	}
}

init 
{ 
	/* Initialization */
	atomic {
		snapshots[0].next = -1;
		snapshots[1].next = -1;
		snapshots[2].next = -1;
		snapshots[3].next = -1;
		g_old_snapshots = -1;
		/* snapshots[0] is by default assigned to
		 * global_updating_snapshot when the system starts. */
		snapshots[0].allocated = 1;
	}

	atomic { run writer(0); run writer(1); }

	byte n;
	n = _nr_pr;
	run reader(0);
	run reader(1);
	(n == _nr_pr); /* To make sure the two reader requests have finished. */

	/* Print out the info of generated snapshots. */
	atomic {
		short result_ptr = g_old_snapshots;
		printf("\nGenerated snapshots are as follows:\n");
		do
			:: (result_ptr >= N_SNAPSHOT) -> break;
		:: (result_ptr == -1) -> break;
		:: else ->
			printf("snapshot id: %d, timestamp: %d, allocated: %d, \
			next snapshot id: %d, counters[0]: %d, counters[1]: %d\n",
					result_ptr,
					snapshots[result_ptr].timestamp,
					snapshots[result_ptr].allocated,
					snapshots[result_ptr].next,
					snapshots[result_ptr].counters[0],
					snapshots[result_ptr].counters[1]);
		result_ptr = snapshots[result_ptr].next;
		od
	} /* end of atomic */

	/* Stop writers to avoid being overwhelmed by useless states. */
	stop_flag = 1;
	
	/* Print out counting results, */
	atomic {
		printf("\nCounting results are as follows:\n");
		printf("Final result of reader %d. Timestamp: %d, sum: %d\n",
				readers[0].id, readers[0].timestamp, readers[0].sum);
		printf("Final result of reader %d. Timestamp: %d, sum: %d\n",
				readers[1].id, readers[1].timestamp, readers[1].sum);
	} /* end of atomic */
	
	if
	:: (readers[0].timestamp < readers[1].timestamp) ->
		assert(readers[0].sum <= readers[1].sum);
	:: (readers[0].timestamp > readers[1].timestamp) ->
		assert(readers[0].sum >= readers[1].sum);
	fi
}

