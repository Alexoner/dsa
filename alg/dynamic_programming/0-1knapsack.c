/*
 * Dynamic Programming | 0-1 Knapsack Problem
 *
 * Given weights and value of n items,put these items in a knapsack of
 * capacity W to get the maximum total value in the knapsack.In other
 * words,given two integer arrays val[0..n-1] and wt[0..n-1] which
 * represents valus and weights associated with n items respectively.Also
 * given an integer W which represents knapsack capacity,find out the
 * maximum value subset of val[] such that sum of weights of this subset is
 * smaller than or equal to W.You cannot break an item,either pick the
 * complete item,or don't pick it (0-1 property).
 *
 * 1) Optimal Substructure:
 * To consider all subsets of items, there can be two cases for every item:
 * (1) the item is included in the optimal subset, (2) not included in the
 * optimal set.
 * Therefore, the maximum value that can be obtained from n items is max of
 * following two values.
 * 1) Maximum value obtained by n-1 items and W weight (excluding nth item).
 * 2) Value of nth item plus maximum value obtained by n-1 items and W
 * minus weight of the nth item (including nth item).
 *
 * If weight of nth item is greater than W, then the nth item cannot be
 * included and case 1 is the only possibility.
 *
 * 2) Overlapping Subproblems
 *
 * In the following recursion tree, K() refers to knapSack().  The two
 * parameters indicated in the following recursion tree are n and W.
 * The recursion tree is for following sample inputs.
 * wt[] = {1, 1, 1}, W = 2, val[] = {10, 20, 30}
 *
 *                       K(3, 2)         ---------> K(n, W)
 *                   /            \
 *                 /                \
 *            K(2,2)                  K(2,1)
 *          /       \                  /    \
 *        /           \              /        \
 *       K(1,2)      K(1,1)        K(1,1)     K(1,0)
 *       /  \         /   \          /   \
 *     /      \     /       \      /       \
 *K(0,2)  K(0,1)  K(0,1)  K(0,0)  K(0,1)   K(0,0)
 * Recursion tree for Knapsack capacity 2 units and 3 items of 1 unit weight.
 *
 * Recurrence:
 * Define knapsack(n,W) as the maximum value we can put in the knapsack,
 * given items number of n and capacity of W.
 * knapsack(n,W) = max(knapsack(n-1,W),
 *                  knapsack(n-1,W-weight[n-1])+value[n-1])
 */

#include <stdio.h>

#define MAX(x, y) ((x) >= (y) ? (x) : (y))

// returns the maximum value that can be put in a knapsack of capacity W
int knapsack_recur(int W, int wt[], int val[], int n)
{
    if (n == 0 || W == 0)
        return 0;
    // If weight of the nth item is more than Knapsack capacity W, then
    // this item cannot be included in the optimal solution
    if (wt[n - 1] > W)
        return knapsack_recur(W, wt, val, n - 1);
    else
        return MAX(knapsack_recur(W - wt[n - 1], wt, val, n - 1) + val[n - 1],
                   knapsack_recur(W, wt, val, n - 1));
}

int knapsack_dp(int W, int wt[], int val[], int n)
{
    int dp[n + 1][W + 1];
    int i, j;
    for (i = 0; i < n + 1; i++)
        dp[i][0] = 0;
    for (j = 1; j < W + 1; j++)
        dp[0][j] = 0;
    for (i = 1; i < n + 1; i++)
        for (j = 1; j < W + 1; j++)
        {
            dp[i][j] = dp[i - 1][j];
            if (wt[i - 1] <= j)
            {
                dp[i][j] = MAX(dp[i][j], dp[i - 1][j - wt[i - 1]] + val[i - 1]);
            }
        }
    return dp[n][W];
}

int main(int argc, char **argv)
{
    int val[] = { 60, 100, 120 };
    int wt[] = { 10, 20, 30 };
    int W = 50;
    int n = sizeof(val) / sizeof(val[0]);

    /*printf("%d\n", knapsack_recur(W, wt, val, n));*/
    printf("%d\n", knapsack_dp(W, wt, val, n));

    return 0;
}
