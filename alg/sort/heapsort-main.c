#include "../define.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#define MAX 128
int main(int argc, char **argv)
{
    time_t t1, t2;
    t1 = time(NULL);
    int n, a[MAX], i;
std:
    printf("please input the size of the array\n");
    if (!scanf("%d", &n))
    {
        printf("input error\n");
        exit(0);
    }
    printf("input the inumbers\n");
    for (i = 0; i < n; i++)
    {
        if (!scanf("%d", a + i))
            exit(0);
    }
file_in:
    printf("\nthe array is below\n");
    for (i = 0; i < n; i++)
        printf("%d ", a[i]);
    printf("\n");
    heap_size = n;
    heapsort_int(a);
    for (i = 0; i < n; i++)
    {
        printf("%d\t", a[i]);
    }
    t2 = time(NULL);
    printf("\ntime:%ld\n", t2 - t1);
    return 0;
}
