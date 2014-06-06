#include <stdio.h>
#include <stdlib.h>

int max_min(int *a, int n,
            int *max, int *min)
{
    int i;
    if (n == 0)
    {
        return -1;
    }
    if (n % 2 == 0)
    {
        //length of the array is even
        if (a[0] > a[1])
        {
            *max = a[0];
            *min = a[1];
        }
        else
        {
            *max = a[0];
            *min = a[1];
        }
        i = 2;
    }
    else
    {
        //length is odd
        *max = *min = a[0];
        i = 1;
    }
    for (; i < n - 1; i += 2)
    {
        int cmp = a[i] < a[i + 1];
        int bigger = cmp ? a[i + 1] : a[i];
        int smaller = cmp ? a[i] : a[i + 1];
        if (smaller < *min)
        {
            *min = smaller;
        }
        if (bigger > *max)
        {
            *max = bigger;
        }
    }

    return 0;
}


















