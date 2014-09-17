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
        // both XOR and OR will do
        /*twos ^= ones & arr[i];*/
        twos |= ones & arr[i];
        ones ^= arr[i];

        int mask = ~(ones & twos);
        ones &= mask;
        twos &= mask;
    }
    return ones;
}

/*
 *Following is another O(n) time complexity and O(1) extra space method
suggested by aj. We can sum the bits in same positions for all the numbers and
take modulo with 3. The bits for which sum is not multiple of 3, are the bits of
number with single occurrence.
Let us consider the example array {5, 5, 5, 8}. The 101, 101, 101, 1000
Sum of first bits%3 = (1 + 1 + 1 + 0)%3 = 0;
Sum of second bits%3 = (0 + 0 + 0 + 0)%0 = 0;
Sum of third bits%3 = (1 + 1 + 1 + 0)%3 = 0;
Sum of fourth bits%3 = (1)%3 = 1;
Hence number which appears once is 1000
*/
int oneInThrees3(int arr[], int n)
{
    int result = 0;
    return 0;
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
