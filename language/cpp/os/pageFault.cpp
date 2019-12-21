#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

/**
 * How to trigger page fault.
 *
 * Reference: https://stackoverflow.com/questions/22091555/what-is-an-easy-way-to-trigger-a-page-fault
 *
 */

int forkPageFault() {
    int pid = 0, retcode = 0, poof = 0;
    if ((pid = fork()) == 0) {
        poof = 1; /* Page fault, fork has copy-on-write behaviour */
    } else {
        waitpid(pid, &retcode, 0);
    }
    return 0;
}

int mallocPageFault() {
    long pagesize = sysconf(_SC_PAGESIZE);
    unsigned char *p = (unsigned char*)malloc(pagesize + 1); /* Cross page boundaries. Page fault may occur depending on your allocator / libc implementation. */
    p[0] = 0;        /* Page fault. */
    p[pagesize] = 1; /* Page fault. */
    return 0;
}

int main()
{
    forkPageFault();
    mallocPageFault();
}
