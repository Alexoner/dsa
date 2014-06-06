#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "../define.h"

int main()
{
    int n, i;
    /*printf("please how mant numbers you want to input\n");*/
    /*if (!scanf("%d", &n))*/
    /*exit(0);*/
    /*int a[n];*/
    /*printf("now plese input the numbers\n");*/
    /*i = 0;*/
    /*while (i < n && scanf("%d", a + i))*/
    /*i++;*/
    /*for (i = 0; i < n; i++)*/
    /*printf("%d", a[i]);*/
    /*printf("\n");*/
    /*quicksort(a, 0, n - 1);*/
    /*for (i = 0; i < n; i++)*/
    /*printf("%d  ", a[i]);*/
    /*printf("\n");*/

    n = 100000;
    int a[n];
    srand(time(NULL));
    for (i = 0; i < n; i++)
    {
        a[i] = rand() % 1000000;
    }
    randomized_quicksort(a, 0, n - 1);
    for (i = 0; i < n; i++)
    {
        printf("%d\t", a[i]);
    }
    printf("\n");
    return 0;
}










