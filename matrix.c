#include <stdio.h>
#include <stdlib.h>
int **multiply(int **a,int **b,int p,int q,int r);
int **multiply(int **a,int **b,int p,int q,int r)
{
    int **res,i;
    res=(int **)malloc(sizeof(int *)*p);
    for(i=0;i<p;i++)
        res[i]=(int *)malloc(sizeof(int)*q);
    int j,k;
    for(i=0;i<p;i++)
        for(k=0;k<r;k++)
            res[i][j]=0;
    for(i=0;i<p;i++)
        for(j=0;j<r;j++)
            for(k=0;k<q;k++)
                res[i][j]+=a[p][q]*b[q][r];
    return res;
}

int main()
{
    //int a[2][3]={{1,2,3},{4,5,6}};
    //int b[3][4]={{1,0,2,3},{4,1,5,6},{6,7,9,0}};
    int **a,**b,**c;
    int i,j,k;
    b=(int **)malloc(sizeof(int *)*2);
    b=(int **)malloc(sizeof(int *)*3);
    for(i=0;i<2;i++)
        a[i]=(int *)malloc(sizeof(int)*3);
    for(i=0;i<3;i++)
        b[i]=(int *)malloc(sizeof(int)*4);
    a[0][0]=1;a[0][1]=2;a[0][2]=3;a[1][0]=4;a[1][1]=5;a[1][2]=6;
    b[0][0]=1;b[0][1]=0;b[0][2]=3;b[0][3]=3;b[1][0]=4;b[1][1]=1;b[1][2]=5;b[1][3]=6;b[2][0]=6;b[2][1]=7;b[2][2]=9;b[2][3]=0;
    c=multiply(a,b,2,3,4);
    for(i=0;i<2;i++)
    {
        for(j=0;j<4;j++)
            printf("%d ",c[i][j]);
        printf("\n");
    }
    return 0;
}



