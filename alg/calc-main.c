/*************************************************************************
    > File Name: calc-main.c
    > Author: hao
    > Mail: onerhao@gmail.com
    > Created Time: Thu 25 Oct 2012 01:40:45 PM CST
 ************************************************************************/
#include "calc.h"
#include <stdio.h>
#include <string.h>

int main()
{
    char infix[MAX], ch, str[] = "1"; //get the input
    int i;
    double res;
    while (1) {
        i = 0;
        memset(infix, 0, sizeof(char) * MAX);
        printf("> ");
        ch = getchar();
        if (ch == EOF)
            break;
        while (ch != '\n') {
            infix[i++] = ch;
            ch = getchar();
            //printf("the expression is %s\n",infix);
        }
        infix[i] = '\0';
        i = calc_num(infix, &res);
        printf("%s \nthe result is:%.2f\n", i ? "legal" : "illegal", res);
    }
    return 0;
}
