#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#define MAX 10000

double dart()
{
    int i,count=0,sum=0;
    double x,y;
    for(i=0;i<10000;i++)
    {
        x=rand()%10000/10000.0;//rand() produce random number for int 
        y=rand()%10000/10000.0;
        printf("x=%f,y=%f\n",x,y);
        if(y<1-pow(x,2))
            count++;
        sum++;
    }
    return (double)count/(double)sum;
}

int main()
{
    double result;
    result=dart();
    printf("the result is %f\n",result);
    return 0;
}
