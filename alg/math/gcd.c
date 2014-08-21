/*************************************************************************
    > File Name: gcd.c
    > Author: hao
    > Mail: onerhao@gmail.com
    > Created Time: Thu 22 Nov 2012 02:20:14 PM CST
 ************************************************************************/
int gcd(int x, int y)
{
    int t;
    while (y > 0)
    {
        if (x > y)
        {
            t = x % y;
            x = y;
            y = t;
        }
        else
        {
            y %= x;
        }
    }
    return x;
}

int gcdn(int *a, int n)
{ // return the greatest common divisor of n numbers in array a
    int t, i;
    if (n < 1)
        return 0;
    t = gcd(a[0], a[1]);
    for (i = 2; i < n; i++)
    {
        t = gcd(t, a[i]);
    }
    return t;
}
