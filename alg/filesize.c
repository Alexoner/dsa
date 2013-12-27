#include <stdio.h>

int main(int argc,char **argv)
{
    FILE *fp;
    long size;
    fp=fopen(*(argv+1),"r");
    fseek(fp,0,SEEK_END);
    size=ftell(fp);
    fclose(fp);
    printf("the file size if %ld bytes\n",size);
    return 0;
}
