
#define N_WRITER 2
#define N_READER 2
#define NUM_SNAPSHOT 4

typedef snapshot {
	short timestamp;
	bool allocated;
	byte next;
	short counters[N_WRITER]
}

snapshot snapshots[NUM_SNAPSHOT];

/* helper functions */
#define ALLOCATED(sp) snapshots[sp].allocated
#define NEXT(sp) snapshots[sp].next

/* global variables */
byte g_timestamp;
byte g_updating_snapshot;
byte g_old_snapshots;
short g_sum[N_READER]

/* Users need to define variable allocated_snapshot_id before using this helper
   function. */
inline snapshot_malloc( )
{
	byte snapshot_ptr = 0;
	do
	:: snapshot_ptr >= NUM_SNAPSHOT -> break;
	:: else ->
		if
		:: (!ALLOCATED(snapshot_ptr)) ->
			ALLOCATED(snapshot_ptr) = true;
			allocated_snapshot_id = snapshot_ptr;
			break;
		:: else -> 
			snapshot_ptr ++;
		fi
	od
}

inline snapshot_free(index)
{
	ALLOCATED(index) = false;
	NEXT(index) = 0;
}

/* Users need to define variable sum before using this helper function */
inline sumup_list(tsp)
{
	byte ptr = g_old_snapshots;
	do
	:: ptr >= NUM_SNAPSHOT -> break;
	:: ptr == -1 -> break;
	:: (snapshots[ptr].timestamp > tsp) -> break;
	:: else ->
		sum = sum + snapshots[ptr].counters[0];
		sum = sum + snapshots[ptr].counters[1];
		ptr = snapshots[ptr].next;
	od
}


/************ Start ECCount **************/

proctype writer(byte id)
{
	do
	:: ((g_sum[0] == 0) || (g_sum[1] == 0)) ->
		snapshots[g_updating_snapshot].counters[id] = 
			snapshots[g_updating_snapshot].counters[id] + 1; 
		skip;
	:: else -> break;
	od
}

proctype reader(byte id)
{
	byte allocated_snapshot_id = 0;
	snapshot_malloc( );
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

	short sum;
	sumup_list(snapshots[tmp].timestamp);
	g_sum[id] = sum;
}

init 
{ 
	/* Initialization */
	atomic {
		snapshots[0].next = -1;
		snapshots[1].next = -1;
		snapshots[2].next = -1;
		snapshots[3].next = -1;
	}

	atomic { run writer(0); run writer(1); }

	byte n;
	n = _nr_pr;
	run reader(0);
	run reader(1);
	(n == _nr_pr); /* To make sure the two reader requests have finished. */

/*
	if
	:: (timestamps[0] < timestamps[1]) ->
		assert(g_sum[0] <= g_sum[1]);
	:: else ->
		assert(g_sum[1] <= g_sum[0]);
	fi
*/
}


/* Helper function to test if the linked list works. */
/*
proctype check_list()
{

	byte ptr = 0;
	do
	:: ptr >= NUM_SNAPSHOT -> break;
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
	:: ptr >= NUM_SNAPSHOT -> break;
	:: else ->
		printf("NUM %d, Allocated %d, Next %d\n", ptr, snapshots[ptr].allocated, snapshots[ptr].next);
		ptr++;
	od

	snapshot_free(ptr_buff1);
	snapshot_free(ptr_buff2);

	ptr = 0;
	do
	:: ptr >= NUM_SNAPSHOT -> break;
	:: else ->
		printf("NUM %d, Allocated %d, Next %d\n", ptr, snapshots[ptr].allocated, snapshots[ptr].next);
		ptr++;
	od
}	
*/
