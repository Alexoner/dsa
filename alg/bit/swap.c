/*
 * The XOR swap is an algorithm that uses the XOR bitwise operation to swap
 * values of distinct variables having the same data type without using a
 * temporary variable.
 */

#include <stdio.h>

int swap(int *x, int *y)
{
    *x = *x ^ *y;
    *y = *y ^ *x;
    *x = *x ^ *y;

    return 0;
}

int main(int argc, char **argv)
{
    int x = 1, y = -2;
    swap(&x, &y);
    printf("%d,%d\n", x, y);
    return 0;
}
