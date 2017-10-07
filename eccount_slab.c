
/* Lock-free slab memeory allocator for snapshots. 
 * For simplicity, we are using system memory management so far in this sample code.*/


#include <stdlib.h>
#include "eccount_slab.h"
#include "eccount_MRMU.h"

#if 0
volatile unsigned long cur_slice_seq;
struct slice * volatile global_slices __attribute__((__aligned__(CACHE_LINE_SIZE)));
struct counter * volatile global_counter_matrix __attribute__((__aligned__(CACHE_LINE_SIZE)));

struct slice * pcount_slice_init( )
{
    int i;
    cur_slice_seq = 1;

    global_slices = (struct slice *)calloc(MAX_READ_CNT, sizeof(struct slice));
    for (i = 0; i < MAX_READ_CNT; i++) {
        global_slices[i].index = i; // This number never changes in subsequent operations.
        global_slices[i].next = -1;
    }
    global_counter_matrix = (struct counter *)calloc(MAX_READ_CNT * NR_THREADS, sizeof(struct counter));

    if (global_slices == NULL || global_counter_matrix == NULL)
        return NULL;
    else
        return global_slices;
}

int pcount_slice_destroy( ) 
{
    return 0;
}

struct slice * pcount_slice_malloc( )
{
    unsigned long seq_limit = __sync_fetch_and_add(&cur_slice_seq, 1);
    seq_limit = seq_limit % MAX_READ_CNT; //FIXME: can optimize a little bit.

    if (global_slices[seq_limit].allocated)
        return NULL;
    if (seq_limit != global_slices[seq_limit].index) {
        printf("Error in slice_malloc(). Unpredicted index value.\n");
        return NULL;
    }
    struct slice * p = &global_slices[seq_limit];
    p->allocated = 1;
    //p->index left unchanged;
    p->anchor = 0;
    p->reader_leaved = 0;
    p->in_use = 0;
    p->timestamp = 0;
    p->next = -1;
    return &global_slices[seq_limit];
}

int pcount_slice_free(struct slice * p)
{
    int i;

    p->allocated = 0;
    //p->index left unchanged;
    p->anchor = 0;
    p->reader_leaved = 0;
    p->in_use = 0;
    p->timestamp = 0;
    p->next = -1;

    // Readers never update (only read) entries in global_counter_matrix,
    // which allows writers update the counter matrix without locking.
    // xx global_counter_matrix[p->index];

    for (i = 0; i < NR_THREADS; i++)
        global_counter_matrix[p->index * NR_THREADS + i].v = 0;

    return 0;
}
#endif

struct snapshot * eccount_snapshot_malloc( )
{
    struct snapshot * sp; 

    sp = (struct snapshot *)calloc(1, sizeof(struct snapshot));
    if (sp == NULL)
    {   
        printf("Error in eccount_snapshot_malloc.\n");
        return NULL;
    }   

    sp->counters = (struct counter *)calloc(NR_THREADS, sizeof(struct counter));
    if (sp->counters == NULL)
    {   
        printf("Error in eccount_snapshot_malloc.\n");
        return NULL;
    }   
    return sp; 
}

void eccount_snapshot_free(struct snapshot * sp) 
{
    free(sp->counters);
    free(sp);
    return;
}

