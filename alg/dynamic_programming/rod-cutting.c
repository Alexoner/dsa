/*
 * Rod cutting
 * Serling Enterprises buys long steel rods and cuts them
 * into shorter rods, which it then sells. Each cut is free. The management of
 *Serling
 * Enterprises wants to know the best way to cut up the rods.
 * We assume that we know, for i D 1; 2; : : :, the price p i in dollars that
 *Serling
 * Enterprises charges for a rod of length i inches. Rod lengths are always an
 *integral
 * number of inches.
 *
 * price table:
 * length i    1  2  3  4  5  6  7  8  9  10
 * price p(i)  1  5  8  9  10 17 17 20 24 30
 */

#include <stdio.h>
#include <stdlib.h>
#define MAX(x, y) (x > y) ? (x) : (y)
#define MAXIN 128
int bottom_up_cut_rod(int *p, int n);
int memoized_cut_rod(int *p, int n, int *r);
int n_prices = 11;
int p[11] = { 0, 1, 5, 8, 9, 10, 17, 17, 20, 24, 30 };
int r[MAXIN];

int cut_rod(int *p, int n)
{
    if (n == 0)
        return n;
    int q = -1, i;
    for (i = 1; i <= n; i++)
    {
        q = MAX(q, p[i] + cut_rod(p, n - i));
    }
    return q;
}

/*
 * There are usually two equivalent ways to implement a
 * dynamic-programming approach.
 *
 */

/*
 * The first approach is top-down with memoization.
 * In this approach, we write the procedure recursively in a
 * natural manner, but modified to save the result of each
 * subproblem (usually in an array or hash table). The procedure
 * now first checks to see whether it has previously solved this
 * subproblem. If so, it returns the saved value, saving further
 * computation at this level; if not, the procedure computes the
 * value in the usual manner. We say that the recursive procedure
 * has been memoized; it “remembers” what results it has computed
 * previously.
 *
 */
int memoized_cut_rod(int *p, int n, int *r)
{
    int q = -1, i;
    if (r[n] >= 0) // already memoized
        return r[n];
    if (n == 0)
    {
        q = 0;
        // stop recursion
    }
    else
    {
        for (i = 1; i <= n; i++)
        {
            q = MAX(q, p[i] + memoized_cut_rod(p, n - i, r));
            // top-down,recursion
        }
    }
    r[n] = q;
    return q;
}

/*
 * The second approach is the bottom-up method.
 * This approach typically depends on some natural notion of the
 * “size” of a subproblem, such that solving any particular
 * subproblem depends only on solving “smaller” subproblems.
 * We sort the subproblems by size and solve them in size order,
 * smallest first.
 * When solving a particular subproblem, we have already solved
 * all of the smaller subproblems its solution depends upon, and
 * we have saved their solutions. We solve each sub-problem only
 * once, and when we first see it, we have already solved all of
 * its prerequisite subproblems.
 *
 * These two approaches yield algorithms with the same asymptotic
 * running time, except in unusual circumstances where the top-down
 * approach does not actually recurse to examine all possible
 * subproblems. The bottom-up approach often has much better
 * constant factors, since it has less overhead for procedure calls
 * .
 */
int bottom_up_cut_rod(int *p, int n)
{
    int r[n + 1];
    int i, j, q;
    r[0] = 0;
    for (j = 1; j <= n; j++)
    {
        // solve the subproblems
        q = -1;
        for (i = 1; i <= j; i++) // loop for the cutting method
        {
            q = MAX(q, p[i] + r[j - i]);
        }
        r[j] = q;
    }
    return r[n];
}

void print_cut_rod_solution(int *p, int n, int *r, int *s)
{
    while (n)
    {
        printf("%d: %d\n", n, s[n]);
        n = n - s[n];
    }
}

int extended_bottom_up_cut_rod(int *p, int n)
{
    int r[n + 1], s[n + 1];
    int i, j, q;
    r[0] = 0;
    for (j = 1; j <= n; j++)
    {
        q = -1;
        for (i = 1; i <= j; i++)
        {
            /*q=MAX(q,p[j]+r[n-j]);*/
            if (i > n_prices - 1)
            {
                break;
            }
            if (q < p[i] + r[j - i])
            {
                q = p[i] + r[j - i];
                s[j] = i;
            }
        }
        r[j] = q;
    }

    print_cut_rod_solution(p, n, r, s);

    return r[n];
}

int main()
{
    int n;
    printf("please input the length of the rod\n");
    if (!scanf("%d", &n))
        exit(0);
    printf("the optimal solution is %d\n",
           /*cut_rod(p, n));*/
           /*bottom_up_cut_rod(p, n, r));*/
           extended_bottom_up_cut_rod(p, n));
    return 0;
}
