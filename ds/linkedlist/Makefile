CC=gcc
CFLAGS=-g -Wall -fPIC

dlinkedlist:dlinkedlist.c dllistmain.c
	$(CC) -o $@ $^ $(CFLAGS)
linkedlist:linkedlist.c linkedmain.c
	$(CC) -o $@ $^ $(CFLAGS)

liblist.so:dlinkedlist.c linkedlist.c
	$(CC) -shared -o $@ $^ $(CFLAGS)
