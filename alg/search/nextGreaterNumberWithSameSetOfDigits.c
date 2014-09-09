/*
 * Find next greater number with same set of digits
 *
 * Given a number n, find the smallest number that has same set of digits as
 * n and is greater than n. If x is the greatest possible number with its set
 * of digits, then print “not possible”.

Examples:
For simplicity of implementation, we have considered input number as a string.

Input:  n = "218765"
Output: "251678"

Input:  n = "1234"
Output: "1243"

Input: n = "4321"
Output: "Not Possible"

Input: n = "534976"
Output: "536479"


Algorithm:
    1)Traverse the given number string form rightmost digit,till you find a
    digit which is smaller than the previous digit.
    2)Search the right side of above found digit d for the smallest number
greater than it.
    3)Swap the above found two digits.
    4)sort all digits after d in ascending order.

Optimization:
    1)Binary Search in step II.
    2)Reverse the array in step IV.

*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Utility to swap two digits
static inline void swap(char *a, char *b)
{
    char temp = *a;
    *a = *b;
    *b = temp;
}

// binary search for the smallest element bigger than ch
int binary_search_char(char *arr, int l, int r, char ch)
{
    int mid;
    while (l <= r)
    {
        mid = (l + r) >> 1;
        if (ch == arr[mid])
            return mid - 1;
        else if (ch > arr[mid])
            r = mid - 1;
        else
            l = mid + 1;
    }
    return l - 1;
}

int reverse_chars(char *arr, int l, int r)
{
    int i, j;
    for (i = l, j = r; i < j; i++, j--)
        swap(arr + i, arr + j);
    return 0;
}

// Find the next greater number,modify in place
void findNext(char number[], int n)
{
    int i, j;
    for (i = n - 2; i + 1 && number[i] >= number[i + 1]; i--)
        ;
    if (i == -1)
    {
        printf("NO\n");
        return;
    }
    j = binary_search_char(number, i, n - 1, number[i]);
    swap(number + i, number + j);
    reverse_chars(number, i + 1, n - 1);

    for (i = 0; i < n; i++)
        printf("%c", number[i]);
    printf("\n");
}

int main(int argc, char **argv)
{
    /*char digits[] = "534976";*/
    char digits[] = "4321";
    int n = strlen(digits);
    findNext(digits, n);

    return 0;
}
