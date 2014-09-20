/*
 * Add two numbers without using arithmetic operators
 *
 * Write a function Add() that returns sum of two integers.The function
 * should not use any of the arithmetic operators(+,++,--,-,..etc).
 *
 * Sum of bits can be obtained by performing XOR(^) of two bits.Carry bit
 * can be obtained by performing AND(&) of two bits.
 * Above is simple Half Adder logic that can be used to add 2 single
 * bits. We can extend this logic for integers. If x and y don’t have set
 * bits at same position(s), then bitwise XOR (^) of x and y gives the
 * sum of x and y. To incorporate common set bits also, bitwise AND (&)
 * is used. Bitwise AND of x and y gives all carry bits. We calculate
 * (x & y) << 1 and add it to x ^ y to get the required result.
 */

#include <stdio.h>

int Add(int x, int y)
{
    int carry = 0;
    while (y)
    {
        carry = x & y;
        // sum of bits of x and y where at least one of bits is not same
        x = x ^ y;

        // carry,common set bits of x and y,shifted by one
        y = carry << 1;
    }
    return x;
}

int main()
{
    int a = 15, b = 32;
    printf("%d + %d = %d\n", a, b, Add(a, b));

    return 0;
}
