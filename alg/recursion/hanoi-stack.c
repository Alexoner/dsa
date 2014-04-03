/*************************************************************************
    > File Name: hanoi-stack.c
    > Author: hao
    > Mail: onerhao@gmail.com
    > Created Time: Wed 31 Oct 2012 11:05:34 AM CST
    >The tower of hanoi problem,using stack other then operating system
    stack.
 ************************************************************************/
#include <stdio.h>
#include <stdlib.h>

struct step
{
    int n;
    char a;
    char b;
    char c;
};

void hanoi(int n,char a,char b,char c);

int main(int argc,char **argv)
{
    int size;
    if(argc>=2)
        size=atoi(argv[1]);
    else
        size=3;
    hanoi(size,'A','B','C');
    return 0;
}

void hanoi(int n,char a,char b,char c)
{
    struct step stack[65535];
    char x,y,z;
    int i=0;
    int top=0,num=0;
    stack[top].n=n;
    stack[top].a=a;
    stack[top].b=b;
    stack[top].c=c;
    while(top>=0)
    {
        while(stack[top].n>1)
        {
            //printf("stack[%d].n:%d \n",top,stack[top].n);
            x=stack[top].a;
            y=stack[top].b;
            z=stack[top].c;
            num=stack[top].n;

            stack[top].n=num-1;
            stack[top].a=y;
            stack[top].b=x;
            stack[top].c=z;

            top++;
            stack[top].n=1;
            stack[top].a=x;
            stack[top].b=y;
            stack[top].c=z;

            top++;
            stack[top].n=num-1;
            stack[top].a=x;
            stack[top].b=z;
            stack[top].c=y;
        }

        while(top>=0&&stack[top].n==1)
        {
            printf("%dth step:%c->%c\n",i+1,stack[top].a,stack[top].c);
            top--;
            i++;
        }
    }
}




