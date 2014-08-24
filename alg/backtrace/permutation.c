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
 * @1:Dynamic Programming.
 */

#include <stdio.h>

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

// Driver program
int main()
{
    char a[] = "ABC";
    permute(a, 0, 2);
    return 0;
}
