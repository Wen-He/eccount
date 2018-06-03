
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


typedef reader_info {
	byte id;
	int sum;
	byte timestamp;
}

reader_info readers[N_READER]

/* global variables */
byte g_timestamp;
short g_updating_snapshot;
short g_old_snapshots;
byte stop_flag;

/* Users need to define variable allocated_snapshot_id before using this helper
   function. */
inline snapshot_malloc( )
{
	byte snapshot_ptr = 0;
	atomic {
	do
	:: (snapshot_ptr >= N_SNAPSHOT) -> 
		allocated_snapshot_id = -1;
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
	}
}

/* Users need to define variable sum before using this helper function */
inline sumup_list(tsp)
{
	short ptr = g_old_snapshots;
	do
	:: ptr >= N_SNAPSHOT -> break;
	:: ptr == -1 -> break;
	:: else ->
		if
		:: (snapshots[ptr].timestamp > tsp) -> 
			ptr = snapshots[ptr].next;
		:: else ->
			sum = sum + snapshots[ptr].counters[0];
			sum = sum + snapshots[ptr].counters[1];
			ptr = snapshots[ptr].next;
		fi
	od
}


/************ Start ECCount **************/

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
	atomic {
		snapshot_malloc( );
		if
		:: (allocated_snapshot_id == -1) -> 
			printf("Error in allocating snapshot.\n");
		:: else ->
			printf("Successfully allocate snapshot %d\n",
				allocated_snapshot_id);
		fi
	}

	byte tmp;
	atomic {
		tmp = g_updating_snapshot;
		g_updating_snapshot = allocated_snapshot_id;
	}

	atomic {
		snapshots[tmp].timestamp = g_timestamp;
		g_timestamp ++;
		snapshots[tmp].next = g_old_snapshots;
		g_old_snapshots = tmp;
	}

	skip;

	int sum;
	sumup_list(snapshots[tmp].timestamp);

	readers[id].id = id;
	readers[id].sum = sum;
	readers[id].timestamp = snapshots[tmp].timestamp;

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
		snapshots[0].allocated = 1;
	}

	atomic { run writer(0); run writer(1); }

	byte n;
	n = _nr_pr;
	run reader(0);
	run reader(1);
	(n == _nr_pr); /* To make sure the two reader requests have finished. */

	short result_ptr = g_old_snapshots;
	do
	:: (result_ptr >= N_SNAPSHOT) -> break;
	:: (result_ptr == -1) -> break;
	:: else ->
		printf("Result: %d, %d, %d, %d, %d, %d\n",
			result_ptr,
			snapshots[result_ptr].timestamp,
			snapshots[result_ptr].allocated,
			snapshots[result_ptr].next,
			snapshots[result_ptr].counters[0],
			snapshots[result_ptr].counters[1]);
		result_ptr = snapshots[result_ptr].next;
	od

	stop_flag = 1;

	printf("Final result of reader %d. Timestamp: %d, sum: %d\n",
		readers[0].id, readers[0].timestamp, readers[0].sum);
	printf("Final result of reader %d. Timestamp: %d, sum: %d\n",
		readers[1].id, readers[1].timestamp, readers[1].sum);

	if
	:: (readers[0].timestamp < readers[1].timestamp) ->
		assert(readers[0].sum < readers[1].sum);
	:: (readers[0].timestamp > readers[1].timestamp) ->
		assert(readers[0].sum > readers[1].sum);
	:: (readers[0].timestamp == readers[1].timestamp) ->
		assert(readers[0].sum == readers[1].sum);
	fi
}


/* Helper function to test if the linked list works. */
/*
proctype check_list()
{

	byte ptr = 0;
	do
	:: ptr >= N_SNAPSHOT -> break;
	:: else ->
		printf("NUM %d, Allocated %d, Next %d\n", ptr, snapshots[ptr].allocated, snapshots[ptr].next);
		ptr++;
	od

	byte allocated_snapshot_id;
	snapshot_malloc( );
	byte ptr_buff1 = allocated_snapshot_id;
	snapshot_malloc( );
	byte ptr_buff2 = allocated_snapshot_id;

	ptr = 0;
	do
	:: ptr >= N_SNAPSHOT -> break;
	:: else ->
		printf("NUM %d, Allocated %d, Next %d\n", ptr, snapshots[ptr].allocated, snapshots[ptr].next);
		ptr++;
	od

	snapshot_free(ptr_buff1);
	snapshot_free(ptr_buff2);

	ptr = 0;
	do
	:: ptr >= N_SNAPSHOT -> break;
	:: else ->
		printf("NUM %d, Allocated %d, Next %d\n", ptr, snapshots[ptr].allocated, snapshots[ptr].next);
		ptr++;
	od
}	
*/
