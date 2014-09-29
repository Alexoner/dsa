/* Problem 1
 *
 * Trailing zeroes in a factorial of a number
 *
 * Given an integer n,write a function that returns count of trailing
 * zeroes in n!.
 *
 * Examples:
 * Input: n = 5
 * Output: 1
 * Factorial of 5 is 20 which has one trailing 0.
 *
 * Input: n = 20
 * Output: 4
 * Factorial of 20 is 2432902008176640000 which has 4 trailing zeroes.
 *
 * Input: n = 100
 * Output: 24
 *
 *
 * Algorithm:
 * The idea is to consider prime factors of a factorial n.A trailing zero
 * always produced by prime factors 2 and 5.If we can count the number of
 * 5s and 2s,out task is done.
 *  The number of 2s in prime factors is always more than or equal to the
 * number of 5s.
 *  How to count total number of 5s in prime factors of n!?A simple way is
 *  to calculate floor(n/5).
 *
 *  n!=[(5*1)*(5*2)*...*(5*k)]*a = [(5^k)*k!]*a,a does not have 5 as prime
 *  factors.
 *  Then f(n!) = k + f(k!),k = n / 5
 *
 *  Then trailing 0s in n! = count of 5s in prime factors of n!
 *                         = floor(n/5)+floor(n/25)+floor(n/125)+...
 *
 *
 *
 * Problem 2
 * The position of the least significant 1 in binary representation
 * Algorithm:
 * Method 1:bit operation
 * Method 2:
 *  Number of 2s as prime factors,f(n!) = k + f(k!),k = n / 5
 */

#include <stdio.h>

int trailingZerosInFactorial(int n)
{
    int count = 0;
    while (n)
    {
        count += n / 5;
        n /= 5;
    }
    return count;
}

int lowestOne(int n)
{
    int count = 0;
    while (n)
    {
        n /= 2;
        count += n;
    }
    return count + 1;
}

int main(int argc, char **argv)
{
    int n = 100;
    if (argc > 1)
        n = atoi(argv[1]);
    printf("Count of trailing 0s in %d is %d \n", n,
           trailingZerosInFactorial(n));
    printf("Lowest 1's position is: %d\n", lowestOne(100));

    return 0;
}
