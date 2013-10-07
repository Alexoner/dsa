CFLAGS= -g -Wall
CC=gcc-4.7
#CC=c++
#CC=g++-4.7
gcd:gcd-main.o gcd.o
	$(CC) $(CFLAGS) $^ -o $@
hanoi:hanoi-stack.o
	$(CC) hanoi-stack.o linkedlist.o -o hanoi
heapsort-main: heapsort-main.o heapsort.o 
	$(CC)  heapsort-main.o heapsort.o -o heapsort-main
bool-infix:bool-infix.o
	$(CC)  bool-infix.o -o bool-infix
bool:bool.o
	$(CC) $(CFLAGS) bool.o -o bool
calc:calc-main.o calc.o strlib.c
	$(CC) $(CFLAGS) $^ -o $@
calc.o:calc.c 
	$(CC) $(CFLAGS) -c calc.c
strlib.o:strlib.c
	$(CC) $(CFLAGS) -c strlib.c
pi:pi.o
	$(CC) $(CFLAGS) pi.o -o pi -lm
horse:horse.o
	$(CC) $(CFLAGS) horse.o -o horse
split:split.o
	$(CC) $(CFLAGS) -std=c99 split.c -o split
fac:fac.o
	$(CC) $(CFLAGS) fac.c linkedlist.c -o fac
binmain:binmain.o
	$(CC) $(CFLAGS) binmain.c binsearch.c -o binmain
quickmain:quickmain.o
	$(CC) $(CFLAGS) quickmain.c quicksort.c -o quickmain
constlist:constlist.o
	$(CC) $(CFLAGS) -O constlist.c -o constlist
test:test.o
	$(CC) $(CFLAGS) -O test.c -o test
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
clean:
	rm horse *.o bool
