#include <stdio.h>
#include <stdlib.h>
#define MAX 5


typedef struct Point
{
    int x;
    int y;
}Point;

int a[8]={2,1,-1,-2,-2,-1,1,2};
int b[8]={1,2,2,1,-1,-2,-2,-1};
int map[MAX][MAX];
int sum=0;

Point poi;
int check(int i);
int track(int n);
void show();
int check(int i)
{
    if(poi.x+a[i]<MAX&&poi.y+b[i]<MAX&&poi.x+a[i]>=0&&poi.y+b[i]>=0)
        if(map[poi.x+a[i]][poi.y+b[i]]==0)
            return 1;
    return 0;
}

int track(int n)
{
    int i,xn,yn;
   /* if(n>MAX*MAX)
    {
        show();
        return;
    }*/
    for(i=0;i<8;i++)
    {
        if(check(i))
        {
            poi.x=poi.x+a[i];
            poi.y=poi.y+b[i];
            xn=poi.x;
            yn=poi.y;
            map[poi.x][poi.y]=n;
            if(n<MAX*MAX)
                track(n+1);
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
    int i,j;
    for(i=0;i<MAX;i++)
        for(j=0;j<MAX;j++)
            map[i][j]=0;
    map[0][0]=1;
    poi.x=0;
    poi.y=0;
    track(2);
    printf("there are %d kinds of methods\n",sum);
    return 0;
}
