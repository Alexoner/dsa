#include <stdio.h>

int foo(char a, char b)
{
    if (a)
    {
        return b;
    }
    else
    {
        return 0;
    }
}

int main()
{
    char a = '0', b = '1', c = '2';
    printf("character is: %c\n", foo(foo(a, b), foo(b, c)));
}
