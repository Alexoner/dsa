#include <stdio.h>
#include "define.h"
/*****************************************************
 * DIVIDE:RECURSE,STACK.
 * CONQUER:SWAP
 * COMBINE:DONE
 * **************************************************/
void quicksort(int *a, int p, int r)
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
