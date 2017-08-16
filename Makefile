
include Makefile.arch

# CFLAGS += -DCHECK_CORRECTNESS

COMMON_DEP = api.h counttorture_optimized.h Makefile Makefile.arch

PROGS =	cscope \
	count_buggy \
	eccount_SRMU \
	eccount_MRMU 

all: $(PROGS)


eccount_SRMU: eccount_SRMU.c $(COMMON_DEP)
	cc $(GCC_ARGS) $(CFLAGS) -o eccount_SRMU eccount_SRMU.c -lpthread

eccount_MRMU: eccount_MRMU.c eccount_MRMU.h eccount_slab.o eccount_slab.h $(COMMON_DEP)
	cc $(GCC_ARGS) $(CFLAGS) -o eccount_MRMU eccount_MRMU.c eccount_slab.o -lpthread

count_buggy: count_buggy.c $(COMMON_DEP)
	cc $(GCC_ARGS) $(CFLAGS) -o count_buggy count_buggy.c -lpthread

clean:
	rm -f $(PROGS) cscope.* *.o *.a

cscope:
	cscope -bqR
