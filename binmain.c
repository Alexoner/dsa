#include <stdio.h>
#include "define.h"

int main()
{
    int a[]={2,3,5,7,8,10,12,15,19,21},i,key;
    printf("please input the number you want to query\n");
    while(scanf("%d",&key))
    {
        i=binsearch(a,10,key);
        if(i!=-1)
        {
            printf("%d is the %dst one\n",key,i+1);
        }
        else
            printf("no number\n");
        printf("please input the number you want to query\n");
    }
    return 0;
}


