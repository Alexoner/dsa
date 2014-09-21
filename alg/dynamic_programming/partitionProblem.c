/*
 * Partition problem
 *
 * Partition problem is to determine whether a given set can be partitioned
 * into two subsets such that the sum of elements in both subsets is same.

 * Examples
 *
 * arr[] = {1, 5, 11, 5}
 * Output: true
 * The array can be partitioned as {1, 5, 5} and {11}
 * arr[] = {1, 5, 3}
 * Output: false
 * The array cannot be partitioned into equal sum sets.
 *
 * Algorithm:
 *  1)Calculate sum of the array.If it is odd,there can not be two subsets
 *  with equal sum,so return false.
 *  2)if sum of array elements is even,calculate sum/2 and find a subset of
 *  array with sum equal to sum/2.
 *
 *  The first step is simple.The second is crucial,it can be solved either
 *  using recursion or Dynamic Programming.
 *
 */

// A recursive solution for partition problem
#include <stdio.h>
#include <stdbool.h>

// A utility function that returns true if there is a subset of arr[]
// with sun equal to given sum
// Time Complexity:O(2^n) in worst case.
bool isSubsetSum(int arr[], int n, int sum)
{
    // Base Cases
    if (sum == 0)
        return true;
    if (n == 0 && sum != 0)
        return false;

    // If last element is greater than sum, then ignore it
    if (arr[n - 1] > sum)
        return isSubsetSum(arr, n - 1, sum);

    /* else, check if sum can be obtained by any of the following
       (a) including the last element
       (b) excluding the last element
    */
    return isSubsetSum(arr, n - 1, sum) ||
           isSubsetSum(arr, n - 1, sum - arr[n - 1]);
}

// Returns true if arr[] can be partitioned in two subsets of
// equal sum, otherwise false
bool findPartiion(int arr[], int n)
{
    // Calculate sum of the elements in array
    int sum = 0;
    for (int i = 0; i < n; i++)
        sum += arr[i];

    // If sum is odd, there cannot be two subsets with equal sum
    if (sum % 2 != 0)
        return false;

    // Find if there is subset with sum equal to half of total sum
    return isSubsetSum(arr, n, sum / 2);
}

// Dynamic Programming Solution
// This is a variation of Knapsack Problem,using 2D Dynamic Programming.
// Create a 2D array part[][] of size (sum/2 + 1)*(n+1),construct the
// solution in bottom-up manner such that every filled entry has
// following property :
// part[i][j] = true if a subset arr[0...j-1] has sum equal to i/2,
// otherwise false.
// recurrence:
//
// part[i][j] = part[i][j-1] || part[i-arr[j]][j-1]
bool partitionSet_dp(int arr[], int n)
{
    int sum = 0;
    int i, j, m;

    // Calculate the sum of all elements
    for (i = 0; i < n; i++)
        sum += arr[i];
    m = sum >> 1;
    bool part[m + 1][n + 1];
    for (j = 0; j < n + 1; j++)
        part[0][j] = true;
    for (i = 1; i < m + 1; i++)
        part[i][0] = false;
    for (i = 1; i < m + 1; i++)
        for (j = 1; j < n + 1; j++)
            part[i][j] = part[i][j - 1] ||
                         (arr[j - 1] <= i && part[i - arr[j - 1]][j - 1]);

    /*for (i = 0; i <= sum / 2; i++)*/
    /*{*/
    /*for (j = 0; j <= n; j++)*/
    /*printf("%s ", part[i][j] ? "t" : "f");*/
    /*printf("\n");*/
    /*}*/

    return part[sum / 2][n];
}

// Driver program to test above function
int main()
{
    int arr[] = { 3, 1, 5, 9, 12 };
    int n = sizeof(arr) / sizeof(arr[0]);
    /*if (findPartiion(arr, n) == true)*/
    if (partitionSet_dp(arr, n) == true)
        printf("Can be divided into two subsets of equal sum");
    else
        printf("Can not be divided into two subsets of equal sum");

    return 0;
}
