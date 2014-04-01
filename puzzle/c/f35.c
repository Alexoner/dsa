#include <stdio.h>

long long times;

/**
 * Utilizing method of induction:
 * run time of n is 2^n.
 * When n == 35,it takes more than 3mins to run the program
 */
long long foo(int n)
{
    long long s = 0;
    times++;
    /*printf("times: %lld\n", times);*/
    while (n--)
    {
        s += foo(n);
    }

    return s > 1 ? s : 1;
}

int main()
{
    printf("result of foo(35) is %lld\n", foo(35));
    printf("foo has run %lld times\n", times);
    return 0;
}
