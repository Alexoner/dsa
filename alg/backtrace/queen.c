#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#define MAX 14
/*#define MAX 4*/

int sum = 0;
int queen[MAX] = {0};
int check(int n);
void place(int n);
void show();

/**
 * check whether a placement is valid
 */
int check(int n)
{
    int i;
    for (i = 0; i < n; i++)
    {
        if (queen[i] == queen[n] || abs(queen[i] - queen[n]) == n - i)
            return 0;
    }
    return 1;
}

/**
 * Solution implemented with recursive backtrack
 * @ param n:the row index to place a queen into
 */
void place(int n)
{
    int i;
    if (n == MAX)
    {
        show();
        return;
    }
    for (i = 0; i < MAX; i++)
    {
        queen[n] = i;
        if (check(n))
            place(n + 1);
    }
}

/**
 * print out the N queen solution
 */
void show()
{
    sum++;
    int i, j;
    for (i = 0; i < MAX; i++)
    {
        for (j = 0; j < MAX; j++)
            if (j == queen[i])
                printf("1 ");
            else
                printf("0 ");
        printf("\n");
    }
    printf("\n");
}

int main()
{
    place(0);
    printf("there are %d solutions\n", sum);
    return 0;
}
