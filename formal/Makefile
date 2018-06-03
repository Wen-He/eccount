
ALL: count_buggy eccount

all: $(ALL)

count_buggy: count_buggy.pml
	spin -a $<
	gcc -o count_buggy pan.c

eccount: eccount.pml
	spin -a $<
	gcc -o eccount pan.c


clean:
	rm -f pan* *.trail eccount count_buggy
