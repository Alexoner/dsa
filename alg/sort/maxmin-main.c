#include <stdio.h>
#include <stdlib.h>
#include <time.h>


int main()
{
    int n = 300000;
    int a[n];
    srand(time(NULL));
    for (int i = 0; i < n; i++)
    {
        a[i] = rand() % 100000;
        printf("%d\t", a[i]);
    }

    int max, min;
    max_min(a, n, &max, &min);
    printf("\nmax: %d,min:%d\n", max, min);
    return 0;
}





