/*
 * There are n stairs, a person standing at the bottom wants to reach the top.
 *The person can climb either 1 stair or 2 stairs at a time. Count the number of
 *ways, the person can reach the top.
 * The person can reach n’th stair from either (n-1)’th stair or from (n-2)’th
 *stair. Let the total number of ways to reach n’t stair be ‘ways(n)’. The value
 *of ‘ways(n)’ can be written as following.
 *
 *     ways(n) = ways(n-1) + ways(n-2)
 *     The above expression is actually the expression for Fibonacci numbers,
 *but there is one thing to notice, the value of ways(n) is equal to
 *fibonacci(n+1).
 *     The above expression is actually the expression for
 *Fibonacci numbers,but there is one thing to notice, the value of ways(n)
 *is equal to fibonacci(n+1).
 *
 *     ways(1) = fib(2) = 1
 *     ways(2) = fib(3) = 2
 *     ways(3) = fib(4) = 3
 *
 *     So we can use function for fibonacci numbers to find the value of
 *ways(n).
 *     Generalization of the above problem
 *     How to count number of ways if the person can climb up to m stairs for a
 *given value m? For example if m is 4, the person can climb 1 stair or 2 stairs
 *or 3 stairs or 4 stairs at a time.
 *
 *     We can write the recurrence as following.
 *
 *        ways(n, m) = ways(n-1, m) + ways(n-2, m) + ... ways(n-m, m)
 *
 *
 *
 *  The Solution to this problem is Dynamic Programming,with the time
 *  complexity of O(mn).
 */

#include <stdio.h>

int exFib(int n, int m)
{
    int i = 0, j;
    int res[n];
    res[0] = 1; // seed value is different from Fibonacci
    res[1] = 1;
    for (i = 2; i < n; i++)
    {
        res[i] = 0;
        for (j = 1; j <= m && j <= i; j++)
        {
            res[i] += res[i - j];
        }
    }
    return res[n - 1];
}

int countWays(int s, int m)
{
    return exFib(s + 1, m);
}

// A recursive function used by countWays
/*int countWaysUtil(int n, int m)*/
/*{*/
/*int res[n];*/
/*res[0] = 1;*/
/*res[1] = 1;*/
/*for (int i = 2; i < n; i++)*/
/*{*/
/*res[i] = 0;*/
/*for (int j = 1; j <= m && j <= i; j++)*/
/*res[i] += res[i - j];*/
/*}*/
/*return res[n - 1];*/
/*}*/

// Returns number of ways to reach s'th stair
/*int countWays(int s, int m)*/
/*{*/
/*return countWaysUtil(s + 1, m);*/
/*}*/

// Driver program to test above algorithm
int main(int argc, char **argv)
{
    int s = 4, m = 4;
    printf("Number of ways = %d", countWays(s, m));
    return 0;
}
