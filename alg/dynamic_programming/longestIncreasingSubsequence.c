/*
 * Dynamic Programming: Longest Increasing Subsequence
 * The longest Increasing Subsequence (LIS) problem is to find the length
 * of the longest subsequence of a given sequence such that all elements
 * of the subsequence are sorted in increasing order. For example, length
 * of LIS for { 10, 22, 9, 33, 21, 50, 41, 60, 80 } is 6 and LIS is
 * {10, 22, 33, 50, 60, 80}.
 *
 * Optimal Substructure:
 * Let arr[0..n-1] be the input array and L(i) be the length of the LIS
 * till index i such that arr[i] is part of LIS and arr[i] is the last
 * element in LIS, then L(i) can be recursively written as.
 * L(i) = { 1 + Max ( L(j) ) } where j < i and arr[j] < arr[i] and if
 * there is no such j then L(i) = 1
 * To get LIS of a given array, we need to return max(L(i)) where
 * 0 < i < n
 * So the LIS problem has optimal substructure property as the main
 * problem can be solved using solutions to subproblems.
 */

#include <stdio.h>
#include <stdlib.h>

#define MAX(a, b) (a) >= (b) ? (a) : (b)

int lis(int *a, int n)
{
    // length[i]:the length of LIS with a[i] as the last element
    int length[n];
    int max_length = 1;
    int end;
    int i, j;
    for (i = 0; i < n; i++)
    {
        length[i] = 1;
        for (j = 0; j < i; j++)
        {
            if (a[j] <= a[i])
            {
                length[i] = MAX(length[i], length[j] + 1);
                if (max_length < length[i])
                {
                    max_length = length[i];
                    end = i;
                }
            }
        }
    }

    return max_length;
}

int lis_print_solution(int *a, int n)
{
    // length[i]:the length of LIS with a[i] as the last element
    int length[n];
    int max_length = 1;
    int end;
    int i, j;
    for (i = 0; i < n; i++)
    {
        length[i] = 1;
        for (j = 0; j < i; j++)
        {
            if (a[j] <= a[i])
            {
                length[i] = MAX(length[i], length[j] + 1);
                if (max_length < length[i])
                {
                    max_length = length[i];
                    end = i;
                }
            }
        }
    }
    int is[max_length];
    for (i = end, j = max_length - 1; i + 1 && j + 1; j--)
    {
        is[j] = i;
        printf("%d ", a[i]);
        for (; i + 1 && length[i] != length[is[j]] - 1; i--)
            ;
    }
    printf("\n");
    for (i = 0; i < max_length; i++)
        printf("%d ", a[is[i]]);
    printf("\n");
    return max_length;
}

int main(int argc, char **argv)
{
    int arr[] = { 10, 22, 9, 33, 21, 50, 41, 80, 60, 30 };
    int n = sizeof(arr) / sizeof(arr[0]);
    printf("Length of LIS is %d\n", lis_print_solution(arr, n));
    /*getchar();*/
    return 0;
}
