#include "../define.h"
#include "../utils.h"
#include <stdio.h>
#include <time.h>

/*****************************************************
 * DIVIDE:RECURSE,STACK.
 * CONQUER:SWAP
 * COMBINE:DONE
 * **************************************************/

//basic quick sort with recursion
int partition(int *a, int p, int r)
{
    int pivot = a[r];
    int i, j;
    int q;
    for (i = p - 1, j = p; j < r; j++)
    {
        if (a[j] < pivot)
        {
            i++;
            SWAP(a[i], a[j], int);
        }
    }
    q = i + 1;
    SWAP(a[r], a[q], int);
    return q;
}

void quicksort(int *a, int p, int r)
{
    if (p < r)
    {
        int q = partition(a, p, r);
        quicksort(a, p, q - 1);
        quicksort(a, q + 1, r);
    }
}

//quick sort with randomization
int randomized_partition(int *a, int p, int r)
{
    srand(time(NULL));
    int i = rand() % (r - p + 1);
    SWAP(a[r], a[i], int);
    return partition(a, p, r);
}

void randomized_quicksort(int *a, int p, int r)
{
    if (p < r)
    {
        int q = randomized_partition(a, p, r);
        randomized_quicksort(a, p, q - 1);
        randomized_quicksort(a, q + 1, r);
    }
}

//quick sort with stack instead of recursion


void quicksort2(int *a, int p, int r)
{
    int i, j, key, tmp;
    key = a[p];
    i = p;
    j = r;
    if (p >= r)
        return ;
    while (1)
    {
        for (; key >= a[i] && i < r; i++); //looking for number >key
        for (; a[j] >= key && j > p; j--); //for number<key,
        if (i < j)
        {
            tmp = a[i];
            a[i] = a[j];
            a[j] = a[i];
        }
        else
            break;
    }
    tmp = a[j];
    a[j] = a[p];
    a[p] = tmp; //so,the array is divided into two by key
    //for(i=p;i<=r;i++)
    //printf("%d\t",a[i]);
    //printf("\n");
    quicksort(a, p, j - 1);
    quicksort(a, j + 1, r);
}


































