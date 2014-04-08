/*
 * In the longest-common-subsequence problem, we are given two sequences
 * X= <x1,x2,... , xm> and Y=<y1,y2, ... , yn> and wish to find a maximum-
 * length common subsequence of X and Y .
 *
 * In a brute-force approach to solving the LCS problem, we would enumerate all
 * subsequences of X and check each subsequence to see whether it is also a subse-
 * quence of Y , keeping track of the longest subsequence we find.
 *
 * Theorem 15.1 (Optimal substructure of an LCS)
 *
 * Let X=<x1,x2,... , xm> and Y= <y1,y2,..., yn> be sequences,
 * and let Z= < z1 ,z2 , ... , zk> be any LCS of X and Y .
 * 1. If x[m] = y[n], then z[k]= x[m]= y[n]and Z[k] is an LCS of X[m].
 * 2. If x[m] != y[n], then z[k] != x[m]implies that Z is an LCS of X[m-1]
 * and Y[n- 1] .
 * 3. If x[m] != y[n], then z[k] != y[n] implies that Z is an LCS of X and Y[n-1].
 */

#include <stdio.h>
#include <stdlib.h>

void print_lcs()
{

}

int lcs_length(char *x, int lx, char *y, int ly)
{
    int c[lx + 1][ly + 1]; //contains length of an LCS of X and Y
    int i, j;

    for (j = 0; j < ly + 1; j++)
    {
        c[0][j] = 0;
    }
    for (i = 0; i < lx + 1; i++)
    {
        c[i][0] = 0;
    }

    //bottom-up X
    for (i = 1; i <= lx; i++)
    {

        //bottom-up Y
        for (j = 1; j <= ly; j++)
        {
            if (x[i - 1] == y[j - 1])
            {
                c[i][j] = c[i - 1][j - 1] + 1;
            }
            else if (c[i - 1][j] >= c[i ][j - 1])
            {
                c[i][j] = c[i - 1][j];
            }
            else
            {
                c[i ][j ] = c[i][j - 1];
            }
        }
    }

    //print the solution two-dimensional array
    printf("   \t");
    for (i = 0; i <= ly; i++)
    {
        printf("%c\t", y[i]);
    }
    printf("\n");
    for (i = 0; i <= lx; i++)
    {
        printf("%c: ", x[i]);
        for (j = 0; j <= ly; j++)
        {
            printf("%d\t", c[i][j]);
        }
        printf("\n");
    }

    //print out the longest common subsequence
    return 0;
}

int main()
{
    char *x = "ABCBDAB", *y = "BDCABA";
    lcs_length(x, 7, y, 6);
    return 0;
}
