all: bloom

bloom: bloom.o test.o
	cc -o bloom -Wall -pedantic bloom.o test.o

bloom.o: bloom.c bloom.h
	cc -o bloom.o -Wall -pedantic -ansi -c bloom.c

test.o: test.c bloom.h
	cc -o test.o -Wall -pedantic -ansi -c test.c
