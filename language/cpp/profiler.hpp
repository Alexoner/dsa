#include <iostream>
#include <gperftools/heap-profiler.h>
#include <gperftools/heap-checker.h>
#include <assert.h>

class ScopedHeapChecker {
public:
    HeapLeakChecker mHeapChecker;
public:
    ScopedHeapChecker():
        //mEnv("HEAPCHECK", "local")
        mHeapChecker("a")
    {
        std::cout << "begin heap check: " << getenv("HEAPCHECK");
    }

    ~ScopedHeapChecker() {
        // TODO: unset environment variable
        std::cout << "end heap check: " << getenv("HEAPCHECK");
        if (!mHeapChecker.NoLeaks()) assert(NULL == "heap memory leak");
    }
};


/**
 * Plug and play. No need to set environment variable CPUPROFILE.
 */
class ScopedHeapProfiler {

    public:
        ScopedHeapProfiler(std::string prefix) {
            HeapProfilerStart(std::vector<char>(prefix.begin(), prefix.begin() + prefix.size() + 1).data());
        }

        ~ScopedHeapProfiler() {
            HeapProfilerDump("debug");
            HeapProfilerStop();
        }

};
