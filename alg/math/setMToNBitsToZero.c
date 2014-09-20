/*
 * Set mth to nth,including, bits to zero in integer.0<=m<=sizeof(int)-1,
 * 0<=n<=sizeof(int)-1
 *
 * Source:Tencent 2015 campus,interview round 2
 */

#include <stdio.h>

int setZeroFromMtoN(int x, int m, int n)
{
    int a = 1;
    int b = 1;
    if (m == 0)
    {
        a = 0;
    }
    else
    {
        a <<= m;
        a -= 1;
    }

    if (n == (sizeof(int) * 8 - 1))
    {
        b = 0;
        /*printf("b: %x\n", b);*/
    }
    else
    {
        b <<= sizeof(int) * 8 - n - 1;
        b -= 1;
        b <<= n + 1;
        printf("b: %x\n", b);
    }
    return x & (a | b);
}

int main()
{
    int x = 0xffff00ff;
    printf("sizeof(int): %ld\n", sizeof(int));
    printf("%x, %x\n", x, setZeroFromMtoN(x, 4, 27));

    return 0;
}
