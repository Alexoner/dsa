CFLAGS=-g -Wall -fPIC
CC=gcc

all:bubsort heapsort qsort-apple qsort-glibc quicksort

bubsort:bubsort.c
	$(CC) -o $@ $^ $(CFLAGS)
heapsort:heapsort.c heapsort.h heapsort-main.c
	$(CC) -o $@ $^ $(CFLAGS)
qsort-apple:qsort-apple.c
	$(CC) -o $@ $^ $(CFLAGS)
qsort-glibc:qsort-glibc.c
	$(CC) -o $@ $^ $(CFLAGS)
quicksort:quicksort.c quickmain.c
	$(CC) -o $@ $^ $(CFLAGS)
