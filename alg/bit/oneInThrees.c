/*
 * Find the elements that appears once
 *
 * Given an array where every element occurs three times,except one
 * element which occurs only once.Find the element that occurs once.
 * Expected time complexity is O(N) and O(1) extra space.
 *
 * Solution:
 *  1)sorting,O(NlogN)
 *  2)hashing,extra space
 *  3)bitwise operators.
 */

#include <stdio.h>

int oneInThrees(int arr[], int n)
{
    int one = 0, two = 0, three = 0;
    int i;
    for (i = 0; i < n; i++)
    {
        three ^= two & arr[i]; // XOR,elements appear 3 times
        two ^= one & arr[i];   // elements appear 2 times
        one ^= arr[i];         // bits that appear even times
        /*if ((three & arr[i]) != arr[i])*/
        /*one ^= arr[i];*/
        one = one ^ three;
        printf("%d,%d,%d\n", one, two, three);
    }
    return one;
    /*return three;*/
}

int oneInThrees2(int arr[], int n)
{
    int ones = 0, twos = 0;
    int i;
    for (i = 0; i < n; i++)
    {
        /*twos ^= ones & arr[i];*/
        twos |= ones & arr[i];
        ones ^= arr[i];

        int mask = ~(ones & twos);
        ones &= mask;
        twos &= mask;
    }
    return ones;
}

int main(int argc, char **argv)
{
    int arr[] = { 12, 1, 12, 3, 12, 1, 1, 2, 3, 3 };
    /*int arr[] = { 3, 2, 3, 3 };*/
    int n = sizeof(arr) / sizeof(arr[0]);
    printf("oneInThrees: %d\n", oneInThrees(arr, n));
    printf("oneInthrees2: %d\n", oneInThrees2(arr, n));
    return 0;
}
