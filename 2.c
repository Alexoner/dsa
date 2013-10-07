#include <stdio.h>
#include <stdlib.h>
#define MAX 5

int map[MAX][MAX]={0};
int sum=0;
int a[8]={2,1,-1,-2,-2,-1,1,2};
int b[8]={1,2,2,1,-1,-2,-2,-1};

int track(int n,int x,int y);
void show();
int track(int n,int x,int y)
{
    int i,xn,yn;
    for(i=0;i<8;i++)
    {
        xn=x+a[i];
        yn=y+b[i];
        if(xn<MAX&&xn>=0&&yn<MAX&&yn>=0)
            if(map[xn][yn]==0)
            {
                if(n<MAX*MAX)
                {
                    track(n+1,xn,yn);
                }
                else
                    show();
                map[xn][yn]=0;
            }
    }
}

void show()
{
    int i,j;
    sum++;
    for(i=0;i<MAX;i++)
    {
        for(j=0;j<MAX;j++)
            printf("%d ",map[i][j]);
        printf("\n");
    }
    printf("\n");
}

int main()
{
    int x,y;
    x=y=0;
    map[x][y]=1;
    track(2,x,y);
    printf("there are %d kinds\n",sum);
    return 0;
}

