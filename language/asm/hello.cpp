/**
 * The output binary object can be examined with
 *    g++ -S hello.cpp
 *    objdump -sd ./a.out
 *
 */

#include <stdio.h>
int foo()
{
    return 0;
}

int sum(int x, int y) {
    return x + y;
}

int main(void) {
    //puts("Hello, World!");
    int a = 0;
    foo();
    sum(1, 2);
    return 0;
}
