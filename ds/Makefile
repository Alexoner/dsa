CFLAGS=-g -Wall

linkedlist:linkedmain.o linkedlist.o
	cc -g $^ -o $@
linkedlist.o:linkedlist.c
	cc -c -g -o $@ $^
linkedmain.o:linkedmain.c
	cc -c -g -o $@ $^

