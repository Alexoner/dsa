CC=gcc
CFLAGS=-g -Wall -fPIC

linkedlist:listmain.c linkedlist.h
	$(CC) -o $@ $^ $(CFLAGS)
slinkedlist:slinkedlist.c slinkedmain.c
	$(CC) -o $@ $^ $(CFLAGS)

liblist.so:linkedlist.c slinkedlist.c
	$(CC) -shared -o $@ $^ $(CFLAGS)

.PHONY:clean

clean:
	rm *.o linkedlist slinkedlist
