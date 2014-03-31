#include <stdlib.h>
#include <stdio.h>

int main()
{
    void *p = malloc(1000000000000000);
    printf("%p\n", p);
    return 0;
}
