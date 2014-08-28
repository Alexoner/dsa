/*
 * Write a C program to print all permutations of a given string
 *
 * A permutation, also called an “arrangement number” or “order,” is a
 *rearrangement of the elements of an ordered list S into a one-to-one
 *correspondence with S itself. A string of length n has n! permutation.
 *
 */

/*
 * Solution:
 * @1:Backtracking.
 * 对于包含n个元素的数组,先确定第一位置的元素，第一个位置有n中可能(每次把
 * 后面的元素和第一个元素交换)，然后求子数组[2…n]的全排列。由于一个数列的
 * 总共有n！个排列，因此时间复杂度为O（n！）
 * @1:Dynamic Programming.
 */

#include <stdio.h>
#include <string.h>

/*Function to swap values at two pointers*/
void swap(char *x, char *y)
{
    char temp;
    temp = *x;
    *x = *y;
    *y = temp;
}

/* Function to print permutations of string
   This function takes three parameters:
   1. String
   2. Starting index of the string
   3. Ending index of the string.
*/

void permute(char *a, int i, int n)
{
    int j;
    if (i == n)
        printf("%s\n", a);
    else
    {
        for (j = i; j <= n; j++)
        {
            swap(a + j, a + i);
            permute(a, i + 1, n);
            swap(a + j, a + i);
        }
    }
}

/*
 * Variation:a string may contain duplicate elements
 * 当我们枚举第i个位置的元素时，若要把后面第j个元素和i交换，则先要保证
 * [i…j-1]范围内没有和位置j相同的元素
 */

int findDup(char *a, int start, int target)
{
    int i;
    for (i = start; i < target; i++)
        if (a[i] == a[target])
            return 1;
    return 0;
}

void permute_nodup(char *a, int start, int end)
{
    int j;
    char *p;
    if (start == end)
    {
        printf("%s\n", a);
    }
    else
    {
        for (j = start; j <= end; j++)
        {
            p = a + j;
            if (!findDup(a, start, j))
            {
                swap(p, a + start);
                permute_nodup(a, start + 1, end);
                swap(p, a + start);
            }
        }
    }
}

// Driver program
int main()
{
    /*char a[] = "ABAC";*/
    char a[] = "112";
    permute_nodup(a, 0, strlen(a) - 1);
    return 0;
}
