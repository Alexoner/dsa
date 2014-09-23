/*
 * Number of 1s in binary representation of a number
 */

#include <stdio.h>

// Method 1:bitwise shift
// Time Complexity:O(logN)
int ones(int v)
{
    int num = 0;
    while (v)
    {
        num += v & 0x1;
        v >>= 1;
    }
    return num;
}

// Method 2: v & (v - 1)
int ones2(int v)
{
    int num = 0;
    while ((unsigned int)v)
    {
        v = v & (v - 1);
        num++;
    }
    return num;
}

int main(int argc, char **argv)
{
    int n = 6;
    printf("number of 1s in binary representation of %d is: %d\n", n, ones2(n));
    return 0;
}
