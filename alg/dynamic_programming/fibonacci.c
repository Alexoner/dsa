/*
 * Program for Fibonacci numbers
 *The Fibonacci numbers are the numbers in the following integer sequence.
 *0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 141, ……..
 *In mathematical terms, the sequence Fn of Fibonacci numbers is defined by
 *the recurrence relation:
 *   F(n) = F(n-1) + F(n-2)
 *  with seed value F(0)=0,F(1)=1.
 */

#include <stdio.h>
#include <stdlib.h>

// 1.recursion
// Time Complexity:T(n)=T(n-1)+T(n-2) which is exponential.
int fib_recursion(int n)
{
    if (n <= 1)
        return n;
    else
        return fib_recursion(n - 1) + fib_recursion(n - 2);
}

// 2.Dynamic Programming
// Time Complexity:O(n)
// Extra Space:O(n)

int fib_dp(int n)
{
    /*Declare an array to store fibonacci numbers.*/
    int f[n + 1];
    int i;

    /*seed value*/
    f[0] = 0;
    f[1] = 1;

    for (i = 2; i <= n; i++)
    {
        /* Add the previous 2 numbers in the series
         * and store it */
        f[n] = f[n - 1] + f[n - 2];
    }

    return f[n];
}

// 3.Space Optimized Dynamic Programming
// Time Complexity:O(n)
// Extra Space:O(1)
int fib_dp_opt(int n)
{
    int a = 0, b = 1, c, i;
    for (i = 2; i <= n; i++)
    {
        c = a + b;
        a = b;
        b = c;
    }

    return c;
}

// 4.Dynamic Programming with Matrix Representation of fibonacci numbers
// The 2-dimensional system of linear difference equations describes the
// Fibonacci sequence.The transition matrix is M=[[1,1],[1,0]]

/* Helper function that multiplies 2 matricies F and M of size 2*2, and
 *   puts the multiplication result back to F[][] */
void multiply(int F[2][2], int M[2][2]);

/* Helper function that calculates F[][] raise to the power n and puts the
 * result in F[][]
 *     Note that this function is desinged only for fib() and won't work as
 *     general power function */

/* Time Complexity:O(n)
 * Space:O(1)
 */
void power(int F[2][2], int n);

int fib_matrix(int n)
{
    int F[2][2] = { { 1, 1 }, { 1, 0 } };
    if (n == 0)
        return 0;
    power(F, n - 1);

    return F[0][0];
}

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

void power(int F[2][2], int n)
{
    int i;
    int M[2][2] = { { 1, 1 }, { 1, 0 } };

    // n - 1 times multiply the matrix to {{1,1},{1,0}}
    for (i = 0; i < n; i++)
    {
        multiply(F, M);
    }
}

/*
 * 5.Time Optimized Method 4
 * Use exponentiation by squaring.
 * Time Complexity:O(logN)
 * Space:O(1)
 */
void power_opt(int F[2][2], int n);

int fib_matrix_opt(int n)
{
    int F[2][2] = { { 1, 1 }, { 1, 0 } };
    if (n == 0)
        return 0;
    power_opt(F, n - 1);
    return F[0][0];
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

/*Driver Program to test above function*/
int main(int argc, char **argv)
{
    int n = 46;
    if (argc > 1)
        n = atoi(argv[1]);
    printf("%d", fib_matrix_opt(n));
    return 0;
}
