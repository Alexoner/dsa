CFLAGS=-g -Wall -fPIC
CC=gcc

all:bubsort heapsort quicksort

bubsort:bubsort.c
	$(CC) -o $@ $^ $(CFLAGS)
heapsort:heapsort.c heapsort.h heapsort-main.c
	$(CC) -o $@ $^ $(CFLAGS)
qsort-apple:qsort-apple.c
	$(CC) -o $@ $^ $(CFLAGS)
qsort-glibc:qsort-glibc.c
	$(CC) -o $@ $^ $(CFLAGS)
quicksort:quicksort.c
	$(CC) -o $@ $^ $(CFLAGS)
maxmin:maxmin.c maxmin-main.c
	$(CC) -o $@ $^ -std=c99 $(CFLAGS)
quickselect:quickselect.c quicksort.c quickselect-main.c
	$(CC) -o $@ $^ -std=c99 $(CFLAGS)
