/*************************************************************************
    > File Name: regex.c
    > Author: hao
    > Mail: onerhao@gmail.com
    > Created Time: Tue 23 Oct 2012 12:28:40 PM CST
 ************************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <regex.h>


int main(int argc,char **argv)
{
    char buf[100],pattern[]="([a-zA-Z0-9])+$";
    int i;
    regex_t *preg=(regex_t *)malloc(sizeof(regex_t));
    regmatch_t pmatch[2];
    if((i=regcomp(preg,pattern,REG_EXTENDED|REG_NEWLINE)))
    {
        printf("can not compile regex error code:%d\n",i);
        return 0;
    }
    while(scanf("%s",buf))
    {
        printf("input:%s\n",buf);
        i=regexec(preg,buf,2,pmatch,REG_NOTEOL);
        printf("i is :%d\n",i);
    }

    /*sscanf("iios//12a  bsDDWDF F @122","%*[^/]//12%[^_@]",buf);
    printf("%s\n",buf);
    sscanf("h(((col1 = yao) or (col2 < 24)) and (col4 = fan))lk",
            "%*[^(]%[0-9    a-z()=<>]",buf);*/
    //characters after type is useless
    printf("%s\n",buf);


    return 0;
}
