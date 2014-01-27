CC=gcc
CFLAGS=-g -Wall -fPIC

linkedlist:linkedlist.c listmain.c
	$(CC) -o $@ $^ $(CFLAGS)
slinkedlist:slinkedlist.c slinkedmain.c
	$(CC) -o $@ $^ $(CFLAGS)

liblist.so:linkedlist.c slinkedlist.c
	$(CC) -shared -o $@ $^ $(CFLAGS)
