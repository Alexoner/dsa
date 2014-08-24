/*
 * We state the matrix-chain multiplication problem as follows: given a chain
 * <A1 , A2 , ... , An > of n matrices, where for i = 1, 2, ... , n,
 * matrix Ai has dimension p(i-1) * pi , fully parenthesize the product
 * A1 A2 ... An in a way that minimizes the number of scalar multiplications.
 */

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

int mp[9] = { 30, 35, 15, 5, 10, 20, 25 };
int mp2[] = { 20, 40, 30, 50 };

// two-dimensional arrays != double pointers
void print_optimal_parens(int *s, int i, int j, int n)
{
    int(*as)[n] = s;
    if (i == j)
    {
        printf("A%d", i);
    }
    else
    {
        printf("(");
        print_optimal_parens(s, i, as[i][j], n);
        print_optimal_parens(s, as[i][j] + 1, j, n);
        printf(")");
    }
}

int matrix_chain_order(int *p, int n)
{
    int m[n][n], s[n - 1][n - 1];
    int i, j, l, k;
    int q;
    for (i = 0; i < n; i++)
    {
        m[i][i] = 0;
    }

    for (l = 2; l <= n; l++)
    {
        // l is the chain length
        for (i = 0; i < n - l + 1; i++)
        {
            j = i + l - 1;
            // i,j are respectively the index the chain start,end with
            /*m[i][j] = ~0;*/
            m[i][j] = INT_MAX;
            for (k = i; k < j; k++)
            {
                // matrix i is p[i] * p[i+1],recursive equation is
                q = m[i][k] + m[k + 1][j] + p[i] * p[k + 1] * p[j + 1];
                if (q < m[i][j])
                {
                    m[i][j] = q;
                    s[i][j] = k;
                }
                printf("m[%d][%d]:%d\n", i, j, m[i][j]);
            }
        }
    }
    print_optimal_parens(s, 0, n - 1, n - 1);
    printf("\n");
    return m[0][n - 1];
}

int main()
{
    printf("result is: %d\n", matrix_chain_order(mp, 6));
    return 0;
}
