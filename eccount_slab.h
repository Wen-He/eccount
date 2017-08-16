
//#define MAX_READ_CNT (1024*1024UL)

struct snapshot * eccount_snapshot_malloc();
void eccount_snapshot_free(struct snapshot * sp);

#if 0
struct slice * pcount_slice_malloc( );
int pcount_slice_free( );
struct slice * pcount_slice_init( );
int pcount_slice_destroy( );
#endif
