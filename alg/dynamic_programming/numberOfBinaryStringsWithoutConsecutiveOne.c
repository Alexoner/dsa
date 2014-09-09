/*
 * Count number of binary strings without consecutive 1s
 *
 * Given a positive integer N,count all possible distinct binary strings
 * of length N such that there are no consecutive 1s.
 *
 * Examples:
 *
 * Input:   N=2
 * Output:  3
 * The 3 strings are 00,01,10
 *
 * Input:   N=3
 * Output:  5 (000,001,010,100,101)
 *
 * This problem can be solved using Dynamic Programming.Let a[i]
 * denote the number of binary strings of length i which do not contain
 * consecutive 1s and ends in 0.Similarly,let b[i] be the number of
 * such strings which ends in 1(actually maybe 01).This yields the
 * recurrence relation:
 * a[i] = a[i-1] + b[i-1]
 * b[i] = a[i-1]
 * let c[i] be the number of all expected strings,then:
 *  c[i] = a[i] + b[i]
 *  i.e. c[i] = c[i-1] + c[i-2].This is exactly the Fibonacci array.
 *  c[1] = 2,c[2] = 3,so seed value:
 *  c[0] = 1,c[1] = 2
 */

#include <stdio.h>
#include <stdlib.h>

void power_opt(int F[2][2], int n);

void multiply(int F[2][2], int M[2][2])
{
    int x = F[0][0] * M[0][0] + F[0][1] * M[1][0];
    int y = F[0][0] * M[1][0] + F[0][1] * M[1][1];
    int z = F[1][0] * M[0][0] + F[1][1] * M[1][0];
    int w = F[1][0] * M[0][1] + F[1][1] * M[1][1];

    F[0][0] = x;
    F[0][1] = y;
    F[1][0] = z;
    F[1][1] = w;
}

int fib_matrix_opt(int n)
{
    int T[2][2] = { { 1, 1 }, { 1, 0 } };
    int seed[2][2] = { { 2, 1 }, { 0, 0 } };
    if (n <= 1)
        return n + 1;
    power_opt(T, n - 1);
    multiply(seed, T);
    return seed[0][0];
}

void power_opt(int F[2][2], int n)
{
    if (n == 0 || n == 1)
        return;

    int M[2][2] = { { 1, 1 }, { 1, 0 } };

    power_opt(F, n / 2);
    multiply(F, F);

    if (n % 2 != 0)
        multiply(F, M);
}

int main(int argc, char **argv)
{
    int n = 5;
    if (argc >= 2)
    {
        n = atoi(argv[1]);
    }
    printf("%d: %d\n", n, fib_matrix_opt(n));
}
