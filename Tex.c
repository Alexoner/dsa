#include <stdio.h>
int main()
{
    char c;
    int k=0;
    while((c=getchar())!=EOF)
    {
        if(c=='"')
        {
            k=!k;
            printf("%s",k?"``":"\"");
        }
        else
            putchar(c);
    }
        return 0;
}


