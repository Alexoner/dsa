#include <stdio.h>
/*#include "define.h"*/

/*
 * Time Complexity:O(log(N))
 */
int binsearch(int *a, int n, int key)
{
    int low, high, mid;
    low = 0;
    high = n - 1;
    while (low <= high)
    {
        mid = (low + high) >> 1;
        if (a[mid] > key)
            high = mid - 1; // recursion .Don't forget "-1"!
        else if (a[mid] < key)
            low = mid + 1;
        else
            return mid;
    }
    return -1;
}
