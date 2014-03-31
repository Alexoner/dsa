#include <stdio.h>

long long times;

int foo(int n)
{
    int s = 0;
    times++;
    printf("times: %lld\n", times);
    while (n--)
    {
        s += foo(n);
    }

    return s > 1 ? s : 1;
}

int main()
{
    printf("result of foo(35) is %d,which has run %lld times\n", foo(35), times);
}
