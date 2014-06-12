#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../utils.h"

//divide and conquer:
//similar algorithm  with quicksort
int quickselect(int *a, int p, int r, int i)
{
    if (p == r)
    {
        return p;
    }
    int q, k;
    q = randomized_partition(a, p, r);
    /*q = partition(a, p, r);*/
    k = q - p + 1;
    if (k == i)
    {
        return q;
    }
    else if (i < k)
    {
        return quickselect(a, p, q - 1, i);
    }
    else
    {
        return quickselect(a, q + 1, r, i - k);
    }
}

//median algorithm
float median(int *a, int p, int r)
{
    if ((r - p) % 2 == 0)
    {
        return a[quickselect(a, p, r, (p + r) / 2)];
    }
    else
    {
        int x = quickselect(a, p, r, (p + r - 1) / 2);
        int y = quickselect(a, p, r, (p + r + 1) / 2);
        return (x + y) / 2;
    }
    return -1.0f;
}






