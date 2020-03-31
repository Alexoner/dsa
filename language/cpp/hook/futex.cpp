#include <boost/stacktrace.hpp>
#include <dlfcn.h>
#include <linux/futex.h>
#include <sys/time.h>
#include <iostream>

#ifndef RTLD_NEXT
#define RTLD_NEXT ((void *) -1l)
#endif

#define REAL_LIBC RTLD_NEXT



/**
 * XXX: doesn't work, futex is a system call without glibc wrapper,
 * must be called with `syscall`
 *
 */
int futex(int *uaddr, int futex_op, int val,
         const struct timespec *timeout,   /* or: uint32_t val2 */
         int *uaddr2, int val3)
{

    std::cout << "futex addr: " << uaddr << " backtrace:\n" << boost::stacktrace::stacktrace();
    static int (*real_func) (int *uaddr, int futex_op, int val,
            const struct timespec *timeout,   /* or: uint32_t val2 */
            int *uaddr2, int val3) = NULL;
    if (!real_func)
    {
        real_func = (int (*) (int *uaddr, int futex_op, int val,
                    const struct timespec *timeout,   /* or: uint32_t val2 */
                    int *uaddr2, int val3)) dlsym (REAL_LIBC, "futex");
    }


    return real_func(uaddr, futex_op, val, timeout, uaddr2, val3);
}
