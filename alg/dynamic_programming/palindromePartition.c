/*Given a string, a partitioning of the string is a palindrome partitioning
 *if every substring of the partition is a palindrome. For example,
 *"aba|b|bbabb|a|b|aba" is a palindrome partitioning of “ababbbabbababa”.
 *Determine the fewest cuts needed for palindrome partitioning of a given
 *string. For example, minimum 3 cuts are needed for “ababbbabbababa”. The
 *three cuts are “a|babbbab|b|ababa”. If a string is palindrome, then
 *minimum 0 cuts are needed. If a string of length n containing all
 *different characters,then minimum n-1 cuts are needed.

Solution
This problem is a variation of Matrix Chain Multiplication problem. If the
string is palindrome, then we simply return 0. Else, like the Matrix Chain
Multiplication problem, we try making cuts at all possible places, recursively
calculate the cost for each cut and return the minimum value.

Let the given string be str and minPalPartion() be the function that returns the
fewest cuts needed for palindrome partitioning. following is the optimal
substructure property.
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <stdbool.h>

#define min(x, y) (x) < (y) ? (x) : (y)

/*
 * Treat it as a variation of Matrix Chain Multiplication problem.
 * Divide the string into two.
 * Time Complexity:O(N^3).
 */
int minPalPartition(char *str)
{
    if (str == NULL)
    {
        return -1;
    }
    int n = strlen(str);
    printf("length:%d\n", n);

    // mincut[i][j]:minimum palindrome cuts of str[i:j+1]
    /*int mincuts[n][n], i, j, l, k;*/
    int i, j, l, k;

    // use array pointer to allocate memory for large two-dimensional array.
    int(*mincuts)[n] = malloc(sizeof(int) * n * n);
    /*int **mincuts = (int **)malloc(sizeof(int *) * n);*/
    /*for (i = 0; i < n; i++)*/
    /*mincuts[i] = (int *)malloc(sizeof(int) * n);*/
    /*memset(mincuts, INT_MAX, sizeof(mincuts));*/
    /*memset(mincuts, n, sizeof(mincuts));*/
    for (i = 0; i < n; i++)
        for (j = i; j < n; j++)
            mincuts[i][j] = n;

    for (i = 0; i < n; i++)
    {
        mincuts[i][i] = 0;
    }
    for (i = 0; i < n - 1; i++)
    {
        if (str[i] == str[i + 1])
            mincuts[i][i + 1] = 0;
    }
    for (l = 3; l <= n; l++)
    {
        for (i = 0; i <= n - l; i++)
        {
            j = l + i - 1;
            if (mincuts[i + 1][j - 1] == 0 && str[i] == str[j])
            {
                mincuts[i][j] = 0;
            }
            else
            {
                for (k = i; k <= j; k++)
                {
                    mincuts[i][j] = min(mincuts[i][j],
                                        mincuts[i][k] + mincuts[k + 1][j] + 1);
                }
            }
        }
    }
    return mincuts[0][n - 1];
}

/*
 * Optimize the Dynamic Programming
 */

int main()
{
    /*char str[] = "ababbbabbababa";*/
    char *str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "abbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    printf("Min cuts needed for Palindrome Partitioning is %d",
           minPalPartition(str));
    return 0;
}
