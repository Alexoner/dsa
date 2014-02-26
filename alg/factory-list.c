#include <stdio.h>
#include <string.h>
#include "sqlist.h"

int main()
{
    int n, add, i, j;
    List L;
    printf("please input a number\n");
    while (scanf("%d", &n))
    {
        init(&L);
        add = 0;
        insert(&L, 1, 1);
        for (i = 2; i <= n; i++)
        {
            for (j = 0; j < L.length; j++)
            {
                *(L.data + j) = *(L.data + j) * i + add;
                add = *(L.data + j) / 10;
                *(L.data + j) /= 10;
                if (j == L.length - 1)
                {
                    if (add)
                        insert(&L, L.length + 1, 0);
                }
            }
        }
        for (j = L.length - 1; j; j--)
            printf("%d", *(L.data + j));
        printf("\nplease input a number\n");
    }
    return 0;
}




