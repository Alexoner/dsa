#include <stdio.h>

int main()
{
    int year;
    printf("please input the year you want to judge\n");
    while(scanf("%d",&year))
    {
        if(!(year%4))
        {
            if(year%100||!(year%400))
            {
                printf("是闰年");
                printf("leap year\n");
            }
        }
        else
            printf("不是闰年\nnot leap year\n");
        printf("please input the year you want to judge\n");
    }
    return 0;
}
