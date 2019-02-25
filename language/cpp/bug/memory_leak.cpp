/**
 *
 *
 $ HEAPCHECK=normal ./bin/tiny_leak
WARNING: Perftools heap leak checker is active -- Performance may suffer
begin heap check: normalleaking
leaking: 0
leaking: 1
leaking: 2
leaking: 3
leaking: 4
leaking: 5
leaking: 6
leaking: 7
leaking: 8
leaking: 9
leaking done
Have memory regions w/o callers: might report false leaks
Leak check a detected leaks of 8192 bytes in 8 objects
The 1 largest leaks:
Leak of 8192 bytes in 8 objects allocated from:
        @ 4018e2
        @ 4019d6
        @ 7f8f1820e830
        @ 401769
        @ 0


If the preceding stack traces are not enough to find the leaks, try running THIS shell command:

pprof ./bin/tiny_leak "/tmp/tiny_leak.17741.a-end.heap" --inuse_objects --lines --heapcheck  --edgefraction=1e-10 --nodefraction=1e-10 --gv

If you are still puzzled about why the leaks are there, try rerunning this program with HEAP_CHECK_TEST_POINTER_ALIGNMENT=1 and/or with HEAP_CHECK_MAX_POINTER_OFFSET=-1
If the leak report occurs in a small fraction of runs, try running with TCMALLOC_MAX_FREE_QUEUE_SIZE of few hundred MB or with TCMALLOC_RECLAIM_MEMORY=false, it might help find leaks more r
tiny_leak: /home/hao.du/Documents/mine/dsa/language/cpp/profiler.hpp:20: ScopedHeapChecker::~ScopedHeapChecker(): Assertion `NULL == "heap memory leak"' failed.
end heap check: normal[2]    17741 abort (core dumped)  HEAPCHECK=normal ./bin/tiny_leak *
 */
//#include <debug.hpp>
#include <iostream>
#include <memory>
#include <thread>
#include <chrono>
#include "profiler.hpp"

//#include <sanitizer/lsan_interface.h>

/**
 * doesn't work, since heap checker use global gflags that parses environment variables
 * when programs starts
 */
//class ScopedEnv {
//public:
    //std::string mKey;
    //ScopedEnv(std::string key, std::string value): mKey(key) {
        //std::string st = (key + "=" + value).data();
        //std::vector<char> chars(st.begin(), st.begin() + st.size() + 1);
        //putenv(chars.data());
    //};
    //~ScopedEnv() {
        //std::string st = (mKey + "=").data();
        //std::vector<char> chars(st.begin(), st.begin() + st.size() + 1);
        //putenv(chars.data());
    //}
//};

/**
 * Start program with environment variable `HEAPCHECK=local`.
 */

char* leak()
{
    ScopedHeapChecker _;
    std::cout << "leaking" << std::endl;
    char *p = NULL;
    for (int i = 0; i < 10; ++i) {
        std::cout << "leaking: " << i << std::endl;
        p = new char[1024];
        delete[] p;
        p = new char[1024];
        p = NULL; // XXX: memory leaks here
    }

    std::cout << "leaking done" << std::endl;

    return p;
}

bool exit_thread = false;

void threadFunc()
{
    while(!exit_thread)
    {
        char* pLeak = new char[256];
        std::this_thread::sleep_for(std::chrono::seconds{1});
    }
}

int main() {

    //HeapProfilerStart("/tmp/profile");
    {
        //ScopedHeapChecker _;
        //ScopedHeapProfiler _("/tmp/profile");
        char *p = leak();
    }


    std::cout << "Done\n";

    return 0;
}
