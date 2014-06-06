#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "../utils.h"

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

