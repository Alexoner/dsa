/*
 * Minimum number of jumps to reach end
 *
 * Given an array of integers where each element represents the max number
 * of steps that can be made forward from that element. Write a function
 * to return the minimum number of jumps to reach the end of the array (
 * starting from the first element). If an element is 0, then cannot move
 * through that element.
 *
 * Example:
 *
 * Input: arr[] = {1, 3, 5, 8, 9, 2, 6, 7, 6, 8, 9}
 * Output: 3 (1-> 3 -> 8 ->9)
 * First element is 1, so can only go to 3. Second element is 3, so can
 * make at most 3 steps eg to 5 or 8 or 9.
 *
 */

#include <stdio.h>
#include <limits.h>

#define MIN(a, b) ((a) <= (b) ? (a) : (b))

// Returns minimum number of jumps to reach arr[h] from arr[l]
int minJumps_recursion(int arr[], int l, int h)
{
    // Base case: when source and destination are same
    if (h == l)
        return 0;

    // When nothing is reachable from the given source
    if (arr[l] == 0)
        return INT_MAX;

    // Traverse through all the points reachable from arr[l]. Recursively
    // get the minimum number of jumps needed to reach arr[h] from these
    // reachable points.
    int min = INT_MAX;
    for (int i = l + 1; i <= h && i <= l + arr[l]; i++)
    {
        int jumps = minJumps_recursion(arr, i, h);
        if (jumps != INT_MAX && jumps + 1 < min)
            min = jumps + 1;
    }

    return min;
}

int minJumps_dp(int arr[], int n)
{
    int jumps[n];
    int i, j;
    for (i = 0; i < n; i++)
    {
        jumps[i] = i;
        for (j = 0; j < i; j++)
        {
            if (arr[j] >= i - j)
            {
                jumps[i] = MIN(jumps[i], jumps[j] + 1);
            }
        }
    }

    return jumps[n - 1];
}

int main(int argc, char **argv)
{
    /*int arr[] = { 1, 3, 6, 3, 2, 3, 6, 8, 9, 5 };*/
    int arr[] = { 1, 3, 5, 8, 9, 2, 6, 7, 6, 8, 9 };
    int n = sizeof(arr) / sizeof(arr[0]);
    printf("Minimum number of jumps to reach end is %d\n", minJumps_dp(arr, n));
    return 0;
}
