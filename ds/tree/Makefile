CC=clang
CFLAGS= -g -Wall -fPIC -O2

btree:btree.c btreemenu.c
	$(CC) -o $@ $^ $(CFLAGS)

.PHONY:clean

clean:
	/bin/rm btree *.o
