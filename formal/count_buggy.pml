
#define N_WRITER 2
#define N_READER 2

int counters[N_WRITER]
int sum[N_READER]

proctype writer(byte id)
{
	do
	:: ((sum[0] == 0) || (sum[1] == 0)) ->
		/* We regard update operation as atomic to save state space. */
		counters[id] = counters[id] + 1;
		skip;
	:: else -> break;
	od
}

proctype reader(byte id)
{
	skip;
	sum[id] = sum[id] + counters[1];
}

init 
{ 
	byte n;
	n = _nr_pr;

	atomic { run writer(0); run writer(1); }

	sum[0] = counters[0];
	run reader(0);

	sum[1] = counters[0];
	run reader(1);

	(n == _nr_pr); /* To make sure the two reader requests have finished. */
	assert(sum[0] <= sum[1]);
}
