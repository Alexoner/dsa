#include <stdio.h>
#define MAX 100
#define min(x,y) (x>y)?y:x
int a[MAX],b[MAX];
int s=0;
void show(int *a,int m);
void divide(int n,int m);
void divide(int n,int m)//the m+1st bit
{
    int i;
    if(n==0)
    {
        show(a,m);
        s++;
    }
    for(a[m]=min(a[m-1],n);a[m]>=1;a[m]--)
    {
       // printf("a[%d] is %d\n",m,a[m]);
        divide(n-a[m],m+1);//RECURSION process
    }
}

void show(int *a,int m)
{
    int i;
    if(b[2]<2)
        printf("\n");//To start a new line.
    else
        //putchar(47); //this is '/'
        putchar(32);
    for(i=1;i<m-1;i++)
    {
        printf("%d+",a[i]);
    }
    printf("%d",a[m-1]);
    for(i=0;i<m;i++)
        b[i]=a[i];
}

int main(int argc,char **argv)
{
    int n;
    if(argc==1)
        n=6;
    else
        n=atoi(*(argv+1));//convert a string into integer
    a[0]=n;
    divide(n,1);
    printf("\nThere are %d kinds of division\n",s);
    return 0;
}
