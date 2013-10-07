#include <stdio.h>
#define MAX 46
char key_str[]="`1234567890-=QWERTYUIOP[]\\ASDFGHJKL;'ZXCVBNM,./";//char array
int main()
{
    char c;
    int i;
    while((c=getchar())!=EOF)
    {
        for(i=1;key_str[i];i++)
        {
            if(c==key_str[i])
            {
             putchar(key_str[i-1]);
             break;
            }
        }
        if(!key_str[i])
        {
            putchar(c);
        }
    }
    return 0;
}

