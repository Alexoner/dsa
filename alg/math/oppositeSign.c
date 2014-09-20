/*
 * Detect if two integers have opposite signs
 *
 * Given two signed integers,write a function that returns true if the
 * signs of given integers are different,otherwise false.
 * The XOR of x and y will have sign bit 1 if they have opposite sign.
 */

#include <stdbool.h>
#include <stdio.h>

bool oppositeSigns(int x, int y)
{
    return ((x ^ y) < 0);
}

int main()
{
    int x = 100, y = -100;
    printf("%d and %d has %s signs\n", x, y,
           oppositeSigns(x, y) ? "opposite" : "same");
    return 0;
}
