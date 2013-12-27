/*for a horse to visit all the point in chess map,visiting each point once*/
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#define MAX 5

typedef struct point //define the struct point
{
	int x;
	int y;
}Point;

int a[]={2,1,-1,-2,-2,-1,1,2};
int b[]={1,2,2,1,-1,-2,-2,-1};
Point poi[MAX*MAX+10];
int step,sum;
int map[MAX][MAX];//indicate whether the point has been accessed before

int right(Point *poi,int n,int i);//judge whether the next point is accessible
void visit(Point *poi,int n,int i);/*visit the next point with coordinate increament 
                              by array a[i],b[i];*/
void showmap();//print the map
void showpath();//show the right path 

int right(Point *poi,int n,int i)
{
    if(n>=MAX*MAX-1)
    {
        return MAX;
    }
	if(poi[n].x+a[i]<MAX && poi[n].y+b[i]<MAX && poi[n].x+a[i]>=0 && poi[n].y+b[i]>=0)
    {
        if(map[poi[n].x+a[i]][poi[n].y+a[i]]==0)
            return 1;
    }
	return 0;
}

void visit(Point *poi,int n,int i)
{
    int j;//CRITICAL!!!
    printf("the %dth step\n",n+1);
	poi[n+1].x=poi[n].x+a[i];
	poi[n+1].y=poi[n].y+b[i];
	map[poi[n+1].x][poi[n+1].y]=n+2;
    showmap();
	for(j=0;j<8;j++)
    {
        if(right(poi,n+1,j)==1)
        {
            visit(poi,n+1,j);
            map[poi[n+2].x][poi[n+2].y]=0;
        }
        else if(right(poi,n+1,j)==MAX)
        {
            printf("done\n");
            showpath();
            return;
        }
    }
}

void showmap()
{
	int i,j;
    sum++;
    printf("the map:\n");
	for(i=0;i<MAX;i++)
    {
		for(j=0;j<MAX;j++)
			printf("%d ",map[i][j]);
        printf("\n");
    }
		printf("\n");
}

void showpath()
{
	int i;
    printf("this is the path\n");
    for(i=0;i<MAX*MAX;i++)
    {
        printf("%d:(%d,%d)\n",i+1,poi[i].x,poi[i].y);
    }
	printf("end\n");
}


int main()
{
    int i,j;
    for(i=0;i<MAX;i++)
        for(j=0;j<MAX;j++)
        {
            //poi[j]={x=0,y=0};
            poi[j].x=0;
            poi[j].y=0;
            map[i][j]=0;
        }
    Point first={0,0};
    poi[0]=first;
    sum=0;
    map[0][0]=1;
	for(i=0;i<8;i++)
		{
			if(right(poi,0,i)==1)
            {
				visit(poi,0,i);
                map[poi[0].x+a[i]][poi[0].y+b[i]]=0;
            }
		}
    printf("there are %d kinds\n",sum);
    return 0;
}




