
# ECCount

This project contains the source code of ECCount, an efficient and consistent counting mechanism, which not only scales on multi-core architectures but also provides accurate counting results without miscounts.

ECCount is realised under GPL v2.

# Organization

* count_buggy.c: Sample code to demonstrate miscounts in widely-used statistical counters.
* eccount_SRMU.c: Single-reader-multi-updater version of ECCount.
* eccount_MRMU.c: Multi-reader-multi-updater version of ECCount.
* counttorture_optimized.h: The framework to test different counters on   multi-core architectures.
* affinity.same.conf: Affinity configuration file which tries to allocate   readers and updaters on the same CPU socket.
* affinity.cross.conf: Affinity configuration file which tries to allocate   readers and updaters on different CPU sockets.

# Compile and Run

On most 64-bits machines running Linux, command "make" is enough to build sample code and ECCount executable file.

Usage:

	./eccount_SRMU --help
	./eccount_SRMU pperf 1 16 affinity.same.conf 15000

	./eccount_MRMU --help
	./eccount_MRMU pperf 1 16 affinity.cross.conf 15000

# Affinity setting files

Upon start, ECCount first loads the specified affinity setting file, and then binds reader threads and updater threads to specified CPU cores, accordingly.

In affinity setting files, the first 16 decimal numbers are used to specified CPU id's to run reader threads, and the subsequent 32 numbers are used to specified CPU id's to run writer threads.

affinity.same.conf and affinity.cross.conf are by default for author's test server which has two Intel Xeon E5-2609 CPU. Users may need to adjust these two files according to their servers' configuration.

# Contact

If you have any questions or suggestions regarding ECCount, please send email to junchangwang@gmail.com.

