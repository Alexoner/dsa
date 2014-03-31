#include <stdio.h>
#include <unistd.h>

int main()
{
    while (1)
    {
        fprintf(stdout, "hello-std-out");
        fprintf(stderr, "hello-std-err");
        sleep(1);
    }
    return 0;
}


/**
 * The code above may not print out "hello-std-out".
 *
 * Solution:
 * stdout is block device,while stderr is not.Block device has
 * a buffer while char device doesn't.
 * Block device will only  input when
 * 1)carriage return
 * 2)full buffer
 * 3)flush is called
 */
