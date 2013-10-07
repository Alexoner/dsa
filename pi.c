#include <stdio.h>
#include <stdlib.h>
#include <math.h>

double calc(int n);
int main()
{
    int n;
    double pi;
    printf("please input the number\n");
    if(!scanf("%d",&n))
        exit(0);
    pi=calc(n);
    printf("PI is %f\n",pi);
    return 0;
}

double calc(int n)
{
    int i,m=4;
    double l=sqrt(2)/2.0;
    for(i=0;i<n;i++)
    {
        l=sqrt(1/2.0-sqrt(1-l*l)/2);//to double the number of l.
        m*=2;
    }
    return l*m;
}
