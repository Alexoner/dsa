CFLAGS= -g -Wall -std=c99 -fPIC
CC=clang
#CC=c++
#CC=g++-4.7

all:hanoi heapsort-main bool-infix bool \
	calc horse split fac binmain quickmain constlist \
	Tex accurate factory factory-list magicsquare bubsort rand

gcd:math/gcd-main.c math/gcd.c
	$(CC) $(CFLAGS) $^ -o $@
hanoi:recursion/hanoi-stack.c
	$(CC) -o $@ $^
heapsort-main: sort/heapsort-main.c heap/heapsort.c 
	$(CC) -o $@ $^
bool-infix:bool-infix.o
	$(CC) -o $@ $^
bool:bool.o
	$(CC) $(CFLAGS) bool.o -o bool
calc:calc-main.o calc.o
	$(CC) $(CFLAGS) $^ -o $@
pi:pi.o
	$(CC) $(CFLAGS) $^ -o $@ -lm
horse:backtrace/horse.c
	$(CC) $(CFLAGS) $^ -o $@
split:split.o
	$(CC) $(CFLAGS) -o $@ $^ -std=c99
fac:fac.o
	#$(CC) $(CFLAGS) fac.c linkedlist.c -o fac
binmain:binmain.o
	$(CC) $(CFLAGS) binmain.c binsearch.c -o binmain
quickmain:quickmain.o
	$(CC) $(CFLAGS) quickmain.c quicksort.c -o quickmain
constlist:constlist.o
	$(CC) $(CFLAGS) -O constlist.c -o constlist
#test:test.o
	#$(CC) $(CFLAGS) -O test.c -o test
Tex:Tex.o
	$(CC) $(CFLAGS) -O Tex.c -o Tex
accurate:accurate.o
	$(CC) $(CFLAGS) -O accurate.c -o accurate
factory:factory.o
	$(CC) $(CFLAGS)  factory.c -o factory
factory-list:
	$(CC) $(CFLAGS) factory-list.c -o factory-list
magicsquare:magicsquare.c
	$(CC) $(CFLAGS) magicsquare.c -o magicsquare
bubsort:
	$(CC) $(CFLAGS) bubsort.c -o bubsort
rand:rand.o quicksort.o
	$(CC) $(CFLAGS) -o $@ $^
calc.o:calc.c 
	$(CC) $(CFLAGS) -c calc.c
clean:
	rm *.o gcd hanoi heapsort-main bool-infix bool \
	calc horse split fac binmain quickmain constlist \
	Tex accurate factory factory-list magicsquare bubsort rand

