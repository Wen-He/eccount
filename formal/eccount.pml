
#define N_WRITER 2
#define N_READER 2

byte request_cnt
short counters0[N_WRITER]
short counters1[N_WRITER]
short counters2[N_WRITER]
short timestamps[N_WRITER]
short sum[N_READER]

proctype writer(byte id)
{
	do
	:: ((sum[0] == 0) || (sum[1] == 0)) ->
		atomic {
		if
		:: (request_cnt == 0) -> 
			/* We regard update operation as atomic to save state space. */
			counters0[id] = counters0[id] + 1;
		:: (request_cnt == 1) -> 
			counters1[id] = counters1[id] + 1;
		:: (request_cnt == 2) -> 
			counters2[id] = counters2[id] + 1;
		fi
		}
		skip;
	:: else -> break;
	od
}

proctype reader(byte id)
{
	byte timestamp;
	atomic {
		timestamp = request_cnt;
		request_cnt = request_cnt + 1;
		timestamps[id] = timestamp;
	}

	skip;

	if
	:: (timestamp == 0) ->
		sum[id] = counters0[0];
		sum[id] = sum[id] + counters0[1];
	:: (timestamp == 1) ->
		sum[id] = counters0[0];
		sum[id] = sum[id] + counters0[1];
		sum[id] = sum[id] + counters1[0];
		sum[id] = sum[id] + counters1[1];
	fi
}

init 
{ 
	atomic { run writer(0); run writer(1); }

	byte n;
	n = _nr_pr;
	run reader(0);
	run reader(1);
	(n == _nr_pr); /* To make sure the two reader requests have finished. */

	if
	:: (timestamps[0] < timestamps[1]) ->
		assert(sum[0] <= sum[1]);
	:: else ->
		assert(sum[1] <= sum[0]);
	fi
}
