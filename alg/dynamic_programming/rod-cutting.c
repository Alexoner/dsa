#include <stdio.h>
#include <stdlib.h>
#define MAX(x,y) (x>y)?(x):(y)
#define MAXIN 128
int bottom_up_cut_rod(int *p,int n,int *r);
int memoized_cut_rod(int *p,int n,int *r);
int p[11]={0,1,5,8,9,10,17,17,20,24,30};
int r[MAXIN];

int memoized_cut_rod(int *p,int n,int *r)
{
    int q=-1,i;
    if(r[n]>=0)//already memoized
        return r[n];
    if(n==0)
    {
        q=0;//stop recursionint bottom-up-cut-rod(int *p,int n,int *r)
    }
    else
    {
        for(i=1;i<=n;i++)
        {
            q=MAX(q,p[i]+memoized_cut_rod(p,n-i,r));//top-down,recursion
        }
    }
    r[n]=q;
    return q;
}

int bottom_up_cut_rod(int *p,int n,int *r)
{
    int i,j,q;
    r[0]=0;
    for(i=1;i<=n;i++)//loop for the length of the rod
    {
        q=-1;
        for(j=1;j<=i;j++)//loop for the cutting method
        {
            q=MAX(q,p[j]+r[n-j]);
        }
        r[i]=q;
    }
    return r[n];
}


int main()
{
    int in;
    printf("please input the length of the rod\n");
    if(!scanf("%d",&in))
            exit(0);
    printf("the optimal solution is %d\n",bottom_up_cut_rod(p,in,r));
    return 0;
}

