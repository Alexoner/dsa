#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define MAX 14
/*#define MAX 4*/

int sum = 0;
int N = 4;
/*int queen[MAX] = {0};*/
int check(int *queen, int row, int col);
void place(int max, int n);
void show(int *queen, int n);

/**
 * check whether a new placement at (row,col) is valid
 * @param queen:queen array representing queens
 * @param row:current chess board row index
 * @param col:current chess board column index
 */
int check(int *queen, int row, int col)
{
    int i;
    for (i = 0; i < row; i++)
    {
        if (queen[i] == col ||
                abs(queen[i] - col) == row - i)
            return 0;
    }
    return 1;
}

/**
 * Solution implemented with recursive backtrack
 * @ param n:the row index to place a queen into
 */
void place(int max, int n)
{
    static int queen[MAX];
    int i;
    if (n == max)
    {
        show(queen, max);
        return;
    }
    for (i = 0; i < max; i++)
    {
        if (check(queen, n, i))
        {
            queen[n] = i;
            place(max, n + 1);
        }
    }
}

/**
 * Solution implemted with DFS search and backtrack
 * @param n:number of rows (queens and columns)
 */
void dfs_place(int n)
{
    int stack[n];
    memset(stack, 0, sizeof(stack));
    int top = -1;
    int i, j;
    stack[++top] = 0;
    while (top >= 0)
    {
        //new placement
        if (top < n - 1)
        {
            for (i = 0; i < n; i++)
            {
                if (check(stack, top + 1, i))
                {
                    stack[++top] = i;
                    break;
                }
            }
        }
        else
        {
            //new placement for another solution
            for (i = stack[top] + 1; i < n; i++)
            {
                if (check(stack, top, i))
                {
                    stack[top] = i;
                    /*show(stack, n);*/
                    break;
                }
            }
        }

        //no new placement,backtracking now!
        while (i == n)
        {
            if (top == 0)
            {
                /*show(stack, n);*/
                return;
            }
            stack[top] = 0;
            top--;
            printf("top: %d\n", top);
            for (i = stack[top] + 1; i < n; i++)
            {
                if (check(stack, top, i))
                {
                    stack[top] = i;
                    show(stack, n);
                    getchar();
                    break;
                }
            }
        }
    }
    return;
}

/**
 * print out the N queen solution
 */
void show(int *queen, int n)
{
    sum++;
    int i, j;
    for (i = 0; i < n; i++)
    {
        for (j = 0; j < n; j++)
            if (j == queen[i])
                printf("1 ");
            else
                printf("0 ");
        printf("\n");
    }
    printf("\n");
}

int main(int argc, char **argv)
{
    if (argc > 1)
    {
        N = atoi(argv[1]);
    }
    place(N, 0);
    /*dfs_place(N);*/
    printf("there are %d solutions\n", sum);
    return 0;
}
