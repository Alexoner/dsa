/*
 * Efficient way to multiply with 7
 * We can multiply a number by 7 using bitwise operator.First left shift
 * the number by 3 bits(you will get 8n) then subtract the original number
 * from the shifted number and return the difference(8n-n).
 */

#include <stdio.h>

int multiplyBySeven(unsigned int n)
{
    return ((n << 3) - n);
}

int main()
{
    unsigned int n = 4;
    printf("%u\n", multiplyBySeven(n));

    return 0;
}
