#include <stdio.h>
int isprime(int n)
{
    int i;
    if(n==1||n==2)
        return 1;
    else
    {
        for(i=2;i*i<=n;i++)
            if(!(n%i))//the paranthesis is critical!
                return 0;
        return 1;
    }
}

int main()
{
    int j,low,high;
    printf("please input two number:\n");
    scanf("%d%d",&low,&high);
    for(j=low;j<=high;j++)
        if(isprime(j))
            printf("%d ",j);
    printf("\n");
    return 0;
}
