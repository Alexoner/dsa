/*
 * Longest Bitonic Subsequence
 * Given an array arr[0 ... n-1] containing n positive integers,a subsequence
 * of arr[] is called Bitonic if it is first increasing, then decreasing.
 * Write a function that takes an array as argument and returns the length of
 * the longest bitonic subsequence.
 * A sequence, sorted in increasing order is considered Bitonic with the
 * decreasing part as empty. Similarly, decreasing order sequence is
 * considered Bitonic with the increasing part as empty.
 *
 * Examples:
 *
 * Input arr[] = {1, 11, 2, 10, 4, 5, 2, 1};
 * Output: 6 (A Longest Bitonic Subsequence of length 6 is 1, 2, 10, 4, 2, 1)
 * Input arr[] = {12, 11, 40, 5, 3, 1} Output: 5 (A Longest Bitonic
 * Subsequence of length 5 is 12, 11, 5, 3, 1)
 * Input arr[] = {80, 60, 30, 40, 20, 10}
 * Output: 5 (A Longest Bitonic Subsequence of length 5 is 80, 60, 30, 20,
 * 10)
 *
 *
 * Solution:
 * Dynamic Programming.
 * This is a variation  of standard Longest Increasing Subsequence(LIS) problem.
 * We need to construct two arrays lis[] and lds[] with bottom-up Dynamic
 * Programming.lis[i] stores the length of the Longest Increasing subsequence
 * ending with arr[i].lds[i] stores the length of the Longest Decreasing
 * subsequence starting from or ending with arr[i].In the former case,we need
 * to return the max value of lis[i] + lds[i] -1,where is is from 0 to n-1.And
 * in the latter case,we need to construct another array lbs[].lbs[i] stores
 * the length of Longest Bitonic Subsequence,which can be computed by lis[j]
 * and lds[j],where j is from 0 to i.
 */

/*Dynamic Programming implementation for longest bitonic subsequence problem*/
#include <stdio.h>
#include <stdlib.h>

#define MAX(a, b) (a) > (b) ? (a) : (b)

/* lbs() returns the length of the Longest Bitonic Subsequence in
    arr[] of size n. The function mainly creates two temporary arrays
    lis[] and lds[] and returns the maximum lbs[i].

    lis[i] ==> Longest Increasing subsequence ending with arr[i]
    lds[i] ==> Longest decreasing subsequence starting with arr[i]

    lis[i] = max(lis[j] + 1),for 0<=j<=i-1 and arr[j] < arr[i]
    lds[i] = max(lds[j] + 1),for 0<=j<=i-1 and arr[j] > arr[i]
    lbs[i] = max(lbs[j] + i-j,lis[k] + i - k),for 0<=j,k<=i-1 and
                                            arr[k] <arr[i] < arr[j]
*/
int lbs(int arr[], int n)
{
    int i, j;
    int lis[n], lbs[n];
    int max_lbs = 0;
    if (n == 0)
    {
        return 0;
    }
    /*lis[0] = lbs[0] = 1;*/
    for (i = 0; i < n; i++)
    {
        lis[i] = 1;
        lbs[i] = 1;
        for (j = 0; j < i; j++)
        {
            if (arr[i] > arr[j])
            {
                lis[i] = MAX(lis[i], lis[j] + 1);
                lbs[i] = MAX(lbs[i], lis[j] + 1);
            }
            else if (arr[i] < arr[j])
            {
                lbs[i] = MAX(lbs[j] + 1, lbs[i]);
            }
            if (lbs[i] > max_lbs)
            {
                max_lbs = lbs[i];
            }
        }
    }
    return max_lbs;
}

int lbs_print_solution(int arr[], int n)
{
    int i, j;
    int lis[n], lbs[n];
    int max_lbs = 1, peak, end;
    if (n == 0)
    {
        return 0;
    }
    /*lis[0] = lbs[0] = 1;*/
    for (i = 0, peak = 0, end = 0; i < n; i++)
    {
        lis[i] = 1;
        lbs[i] = 1;
        for (j = 0; j < i; j++)
        {
            if (arr[i] > arr[j])
            {
                lis[i] = MAX(lis[j] + 1, lis[i]);
                lbs[i] = MAX(lis[j] + 1, lbs[i]);

                if (lbs[i] > max_lbs)
                {
                    max_lbs = lbs[i];
                    /*printf("max_lbs: %d,j: %d,i: %d\n", max_lbs, j, i);*/
                    end = i;
                    peak = i;
                }
            }
            else if (arr[i] < arr[j])
            {
                lbs[i] = MAX(lbs[j] + 1, lbs[i]);

                if (lbs[i] > max_lbs)
                {
                    max_lbs = lbs[i];
                    /*printf("max_lbs: %d,j: %d,i: %d\n", max_lbs, j, i);*/
                    end = i;
                    if (arr[peak] < arr[j])
                        peak = j;
                }
            }
        }
    }

    for (i = 0; i < n; i++)
        printf("%d ", lis[i]);
    printf("\n");
    /*printf("\npeak: %d,end: %d\n", peak, end);*/

    int bs[max_lbs];
    bs[max_lbs - 1] = end;
    i = max_lbs - 2;

    // navigate from end to peak to fill decreasing subsequence
    for (j = end - 1; j >= peak; j--)
    {
        if (lbs[j] == lbs[bs[i + 1]] - 1 && arr[j] > arr[bs[i + 1]])
        {
            bs[i] = j;
            i--;
        }
    }

    // j == peak - 1
    /*printf("j: %d,lis[j]: %d\n", j, lis[j]);*/
    // navigate from peak - 1 to fill increasing subsequence
    for (; i + 1 && j + 1; i--)
    {
        for (; j + 1 && lis[j] != lis[bs[i + 1]] - 1; j--)
            ;
        bs[i] = j;
    }

    for (i = 0; i < max_lbs; i++)
        printf("%d ", arr[bs[i]]);
    printf("\n");
    /*}*/

    return max_lbs;
}

/* lbs() returns the length of the Longest Bitonic Subsequence in
    arr[] of size n. The function mainly creates two temporary arrays
    lis[] and lds[] and returns the maximum lis[i] + lds[i] - 1.

    lis[i] ==> Longest Increasing subsequence ending with arr[i]
    lds[i] ==> Longest decreasing subsequence starting with arr[i]
*/

int main(int argc, char **argv)
{
    /*int arr[] = { 0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15 };*/
    /*int arr[] = { 80, 60, 30, 40, 20, 10 };*/
    int arr[] = { 1, -1, 3, 2, -3 };
    /*int arr[] = { 1, 2, 3, 4, 5, 6 };*/
    int n = sizeof(arr) / sizeof(arr[0]);
    printf("Length of LBS is %d\n", lbs_print_solution(arr, n));
    return 0;
}
