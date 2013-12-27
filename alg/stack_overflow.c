/*************************************************************************
    > File Name: foo.c
    > Author: hao
    > Mail: onerhao@gmail.com
    > Created Time: Wed 31 Oct 2012 10:40:54 AM CST
 ************************************************************************/
#include <stdio.h>

void foo();

int main()
{
    foo();
    return 0;
}

void foo()
{
    static int i=0;
    FILE *fp=fopen("stack.log","a");
    fprintf(fp,"%d\n",i++);
    fclose(fp);
    foo();
}
