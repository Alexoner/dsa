#include <stdio.h>

int sequence(int *numbers, int n)
{
    // Initialize variables here
    int max_so_far  = numbers[0], max_ending_here = numbers[0];

    // OPTIONAL: These variables can be added in to track the position of the subarray
    // size_t begin = 0;
    // size_t begin_temp = 0;
    // size_t end = 0;

    // Find sequence by looping through
    for (size_t i = 1; i < n; i++)
    {
        // calculate max_ending_here
        if (max_ending_here < 0)
        {
            max_ending_here = numbers[i];

            // begin_temp = i;
        }
        else
        {
            max_ending_here += numbers[i];
        }

        // calculate max_so_far
        if (max_ending_here >= max_so_far )
        {
            max_so_far  = max_ending_here;

            // begin = begin_temp;
            // end = i;
        }
    }
    return max_so_far ;
}
