#include <stdio.h>
#include <stdlib.h>
#define MAX 256
int main()
{
    int n,i,j,tmp;//i is the index
    printf("please input the number of how many\n");
    if(!scanf("%d",&n))
    {
        printf("error input\n");
        exit(1);
    }
    int a[n];
    printf("now input %d numbers:\n",n);
    for(i=0;i<n;i++)
        if(!scanf("%d",a+i))
        {
            printf("illegal input!\n");
            exit (1);
        }
    for(i=0;i<n-1;i++)
    {
        for(j=0;j<n-1;j++)
        {
            if(a[j]>a[j+1])
            {
                tmp=a[j];
                a[j]=a[j+1];
                a[j+1]=tmp;
            }
        }
        for(j=0;j<n;j++)
            printf("%4d",*(a+j));
        printf("\n");
    }
    return 0;
}
                  
