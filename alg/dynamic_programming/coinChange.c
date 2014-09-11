/*
 * Coin Change
 *
 * Given a value N,if we want to make change for N cents,and we have infinite
 * supply of each of S = {S1,S2,...,Sn} valued coins,how many ways can we
 * make the change? The order of coins doesn't matter.
 *
 * For example,for N=4 and S={1,2,3},there are four solutions:{1,1,1,1},
 * {1,1,2},{2,2},{1,3}.So output should be 4.For N=10 and S={2,5,3,6},there
 * are five solutions:{2,2,2,2,2},{2,2,3,3},{2,2,6},{2,3,5} and {5,5}.So the
 * output should be 5.
 *
 * 1)Optimal Substructure
 *  We can divide all set solutions in two sets.
 *      Solutions that do not contain mth coin(Sm)
 *      Solutions that contain at least one Sm.
 *  Then count(S[],m,n)=count(S[],m-1,n)+count(S[],m,n-Sm).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*
 * Time Complexity:O(m*n)
 */
int coinChange(int S[], int m, int n)
{
    int table[m][n + 1];
    int i, j;
    int x, y;
    // in base case when n == 0,the count number is 1
    for (i = 0; i < m; i++)
    {
        table[i][0] = 1;
    }
    for (i = 0; i < m; i++)
        for (j = 1; j < n + 1; j++)
        {
            x = i ? table[i - 1][j] : 0;
            y = (j - S[i] >= 0) ? table[i][j - S[i]] : 0;
            table[i][j] = x + y;
        }
    return table[m - 1][n];
}

int coinChange_space_opt(int S[], int m, int n)
{
    // table[i] will be storing the number of solutions for
    // value i. We need n+1 rows as the table is consturcted
    // in bottom up manner using the base case (n = 0)
    int table[n + 1];

    // Initialize all table values as 0
    memset(table, 0, sizeof(table));

    // Base case (If given value is 0)
    table[0] = 1;

    // Pick all coins one by one and update the table[] values
    // after the index greater than or equal to the value of the
    // picked coin
    for (int i = 0; i < m; i++)
        for (int j = S[i]; j <= n; j++)
            table[j] += table[j - S[i]];

    return table[n];
}

int main(int argc, char **argv)
{
    int arr[] = { 1, 2, 3 };
    int m = sizeof(arr) / sizeof(arr[0]);
    int n = 4;
    printf("%d\n", coinChange(arr, m, n));
    printf("%d\n", coinChange_space_opt(arr, m, n));
    return 0;
}
