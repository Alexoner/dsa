/**
 * memcpy hook to print information about call stack
 *
 * There are two methods to override a system call in C.
 * 1) Using LD_PRELOAD.
 *    There is a shell environment variable in Linux called LD_PRELOAD, which can be set to a path of a shared library, and that library will be loaded before any other library (including glibc).
 * 2) Using 'ld --wrap=symbol':
 *    This can be used to use a wrapper function for symbol. Any further reference to symbol will be resolved to the wrapper function. [man 1 ld].LINKFLAGS='-Xlinker --wrap=memcpy -rdynamic'
 *    Link with 'LINKFLAGS='-Xlinker --wrap=memcpy -rdynamic'.
 *
 * Reference: http://samanbarghi.com/blog/2014/09/05/how-to-wrap-a-system-call-libc-function-in-linux/
 *
 * Problems:
 * memcpy is a very low level call, many function will call it. So we must avoid stack overflow caused by infinite calling hook function.
 */


#ifndef RTLD_NEXT
#define RTLD_NEXT ((void *) -1l)
#endif

#define REAL_LIBC RTLD_NEXT


#include <dlfcn.h>
#include <string.h>
#include <memory>
#include <iostream>
#include <boost/stacktrace.hpp>

#include <easylogging++.h>
INITIALIZE_EASYLOGGINGPP


using namespace std;

class StackDepthGuard
{
public:
    StackDepthGuard(bool enabled, int &depth):
        mEnabled(enabled),
        mDepth(depth)
    {
        ++mDepth;
    }
    ~StackDepthGuard()
    {
        --mDepth;
    }

    operator bool() const
    {
        return mDepth == 1 && mEnabled;
    }

    bool &mEnabled; // global switch reference
    int &mDepth; // stack depth counter
};

namespace
{
    bool enableHook = true; // global switch, not used yet
    thread_local int depth = 0;
}

extern "C"
{

// Link with 'LINKFLAGS='-Xlinker --wrap=memcpy -rdynamic' for this implementation.
void* __real_memcpy(void* dest, const void* src, size_t n);
// FIXME: not finished
void* __wrap_memcpy(void* dest, const void* src, size_t n)
{
    StackDepthGuard enabled(enableHook, depth);
    if (enabled)
    {
        //LOG(INFO) << "memcpy n: " << n << " backtrace:\n" << boost::stacktrace::stacktrace();
        fprintf(stdout, "calling memcpy");
    }

    // call underlying memcpy
    return __real_memcpy(dest, src, n);
    // char *cdst = (char*)dest;
    // const char *csrc = (const char*)src;
    // const char *cend = csrc + n;
    // while (csrc < cend) *cdst++ = *csrc++;
    // return dest;
}

// Use LD_PRELOAD method for this implementation
// XXX: if dlsym calls an underlying system call that we're trying to override, use ld --wrap=symbol
void* memcpy(void* dest, const void* src, size_t n)
{
    //if (enabled)
    StackDepthGuard enabled(enableHook, depth);

    if (enabled)
    {
        //LOG(INFO) << "hooking memcpy";
        //fprintf(stdout, "HOOK: memcpy( dest=%p , src=%p, n=%zd )\n", dest, src, n);
        fprintf(stdout, "HOOK: memcpy( dest=%p , src=%p, n=%zd )\n", dest, src, n);
        std::cout << boost::stacktrace::stacktrace() << endl;
        //memcpy(NULL, NULL, 0); // XXX: test infinite recursion stack overflow
        //printf("HOOK: memcpy( dest=%p , src=%p, n=%zd )\n", dest, src, n);
    }

    // call underlying memcpy
    static void* (*func_memcpy) (void*, const void *, size_t) = NULL;
    if (!func_memcpy)
    {
        func_memcpy = (void* (*) (void*, const void *, size_t)) dlsym (REAL_LIBC, "memcpy");
    }

    return func_memcpy(dest, src, n);
}

}
