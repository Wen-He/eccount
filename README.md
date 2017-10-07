
# ECCount

Source code of ECCount, an efficient and consistent counting mechanism, which
not only scales on multi-core architectures but also provides accurate counting
results without miscounts.

# Organization

* count_buggy.c: Sample code to demonstrate miscounts in statistical counters.
* eccount_SRMU.c: Single-reader-multi-updater version of ECCount
* eccount_MRMU.c: Multi-reader-multi-updater version of ECCount
* counttorture_optimized.h: The framework to test different counters on
  multi-core architectures (A gaint
  file)


