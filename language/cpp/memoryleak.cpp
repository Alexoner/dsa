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
        p = NULL;
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
