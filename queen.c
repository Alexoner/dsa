#include <stdio.h>
#include <math.h>
#define MAX 8

int sum=0;
int queen[MAX]={0};
int check(int n);
void place(int n);
void show();

int check(int n)
{
    int i;
    for(i=0;i<n;i++)
    {
        if(queen[i]==queen[n]||abs(queen[i]-queen[n])==n-i)
            return 0;
    }
    return 1;
}

void place(int n)
{
    int i;
    if(n==MAX)
    {
        show();
        return;
    }
    for(i=0;i<MAX;i++)
    {
        queen[n]=i;
        if(check(n))
            place(n+1);
    }
}

void show()
{
    sum++;
    int i,j;
    for(i=0;i<MAX;i++)
    {
        for(j=0;j<MAX;j++)
            if(j==queen[i])
                printf("1 ");
            else
                printf("0 ");
        printf("\n");
    }
    printf("\n");
}

int main()
{
    place(0);
    printf("there are %d kinds\n",sum);
    return 0;
}
