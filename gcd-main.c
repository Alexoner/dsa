/*************************************************************************
    > File Name: gcd-main.c
    > Author: hao
    > Mail: onerhao@gmail.com
    > Created Time: Thu 22 Nov 2012 02:25:19 PM CST
 ************************************************************************/
#include <stdio.h>

extern int gcd(int x,int y);

int main()
{
    int a[3];
    printf("please input 3 integer:\n");
    scanf("%d%d%d",a,a+1,a+2);
    printf("The greatest common devisor is:%d\n",gcdn(a,3));
    return 0;
}
