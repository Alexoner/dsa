#CC=clang
CC=gcc
CFLAGS= -g -Wall -fPIC -O2

tree_from_post_in: tree_from_post_in.cpp
	$(CXX) -o $@ $^ $(CFLAGS)

btree:btree.c btreemenu.c
	$(CC) -o $@ $^ $(CFLAGS)
bstree:bstree.c bstree.h btree.c
	$(CC) -o $@ $^ $(CFLAGS)
rbtree:rbtree.c rbtree.h bstree.c bstree.h btree.c
	$(CC) -o $@ $^ $(CFLAGS)

.PHONY:clean

clean:
	/bin/rm btree *.o
