
ALL: count_buggy eccount

all: $(ALL)

count_buggy: count_buggy.pml
	spin -a $<
	gcc -o $@ pan.c

eccount: eccount.pml
	spin -a $<
	gcc -o $@ pan.c

list2: list2.pml
	spin -a $<
	gcc -o $@ pan.c

clean:
	rm -f pan* *.trail eccount count_buggy
