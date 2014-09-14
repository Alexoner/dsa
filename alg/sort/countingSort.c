/* Introduction to Algorithms,third edition:
 *  Counting sort assumes that each of the n input elements is an integer
 * in the range 0 to k,for some integer k.When k = O(n),the sort runs in
 * O(n) time.
 *  Counting sort determines,for each input element x,the number of
 * elements less than x.It uses this information to place element x
 * directly into its position int the output array.For example,if 17
 * elements are less than x,then x belongs in output position 18.We must
 * modify this scheme slightly to handle the situation in which several
 * elements have the same value,since we do not want to put them all in the
 * same position.
 *  In the code for counting sort,we assume that the input is an array
 * A[1..n] ,and thus A.length = n.We require two other arrays: the array
 * B[1..n] holds the sorted output,and the array C[0..k] provides
 * temporary working storage.
 */

#include <stdio.h>

// Time Complexity:O(n)
int counting_sort(int A[], int B[], int n, int k)
{
    int C[k + 1];
    int i, j;
    for (i = 0; i <= k; i++)
        C[i] = 0;
    for (j = 0; j < n; j++)
        C[A[j]] = C[A[j]] + 1;
    // C[i] now contains the number of elements equal to i.
    for (i = 1; i <= k; i++)
        C[i] = C[i] + C[i - 1];
    // C[i] now contains the number of elements less than or equal to i.
    for (j = n - 1; j + 1; j--)
    {
        B[C[A[j]] - 1] = A[j];
        C[A[j]] = C[A[j]] - 1;
    }
    return 0;
}

int main(int argc, char **argv)
{
    int A[] = { 6, 0, 2, 0, 1, 3, 4, 6, 1, 3, 2 };
    int n = sizeof(A) / sizeof(A[0]);
    int i;
    int B[n];
    counting_sort(A, B, n, 6);
    for (i = 0; i < n; i++)
        printf("%d ", B[i]);
    printf("\n");
    return 0;
}
