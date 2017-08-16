
#include "api.h"

struct counter{
    unsigned long v; 
}__attribute__((__aligned__(CACHE_LINE_SIZE)));

struct snapshot{
    // Used by allocator
    int allocated;
	
    // Used by readers
    int anchor;
    int reader_leaved;
    unsigned long timestamp;
	struct counter * counters;
	struct snapshot * next;
}__attribute__((__aligned__(CACHE_LINE_SIZE)));
