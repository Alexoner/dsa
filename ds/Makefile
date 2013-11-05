CFLAGS=-g -Wall

linkedlist:linkedmain.o linkedlist.o
	cc -g $^ -o $@
linkedlist.o:linkedlist.c
	cc -c -g $^
linkedmain.o:linkedmain.c
	cc -c -g $^
tree:tree.c treemenu.c
	$(CC) -o $@ $^ $(CFLAGS)
