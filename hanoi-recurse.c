/*hanoi problem,to move n size-increasing dish between 3 poles*/
#include <stdio.h>
#include <stdlib.h>

int step;
FILE *fp;
void hanoi(int n,char a,char b,char c)
{
    if(n==1)
    {
        printf("%dth step:%c->%c\n",++step,a,c);//the BASE CONDITION;
    }
    else
    {
        hanoi(n-1,a,c,b);//the RECURSIVE PROCESS
        printf("%dth step:%c->%c\n",++step,a,c);
        hanoi(n-1,b,a,c);
    }
}

int main(int argc,char **argv)
{
    int n;
    step=0;
    //fp=fopen("sys.conf","w");

    if(argc==2)
    {
        n=atoi(*(argv+1));
    }
    else
        n=4;
    printf("there are %d dishes\n",n);
    hanoi(n,'A','B','C');
    return 0;
}

