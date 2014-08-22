#include <stdio.h>
#include <stdlib.h>
#include <time.h>

int main()
{
    int n = 1000;
    int a[n], j, r;
    srand(time(NULL));
    for (int i = 0; i < n; i++)
    {
        a[i] = rand() % 1000;
        printf("%d\t", a[i]);
    }
    j = 100;
    r = quickselect(a, 0, n - 1, j);
    printf("\n\n%dth: %d\n", j, a[r]);
    for (int i = 0; i < n; i++)
    {
        if (r == i)
        {
            printf("\033[0;31m");
        }
        printf("%d\t\033[0m", a[i]);
    }
    return 0;
}

