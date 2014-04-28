#CC=clang
CC=gcc
CFLAGS= -g -Wall -fPIC -O2

btree:btree.c btreemenu.c
	$(CC) -o $@ $^ $(CFLAGS)
bstree:bstree.c bstree.h btree.c
	$(CC) -o $@ $^ $(CFLAGS)
rbtree:rbtree.c rbtree.h bstree.c bstree.h btree.c
	$(CC) -o $@ $^ $(CFLAGS)

.PHONY:clean

clean:
	/bin/rm btree *.o
