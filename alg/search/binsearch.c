#include <stdio.h>
/*#include "define.h"*/

/*
 * Time Complexity:O(log(N))
 */
int binsearch(int *a, int left, int right, int key)
{
    int mid;
    while (left <= right)
    {
        mid = (left + right) >> 1;
        if (a[mid] > key)
            right = mid - 1; // recursion .Don't forget "-1"!
        else if (a[mid] < key)
            left = mid + 1;
        else
            return mid;
    }
    return -1;
}
