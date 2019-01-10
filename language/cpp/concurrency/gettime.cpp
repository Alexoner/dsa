#include <iostream>
#include <chrono>
#include <sys/time.h>
#include <unistd.h>
#include <vector>
#include <thread>
#include <atomic>

#define NUM_SAMPLES 1000000
unsigned int NUM_THREADS = 4;

/**
 * get time stamp counter
 */
static inline unsigned long long gettsc(void)
{
    unsigned int lo, hi;

    // RDTSC copies contents of 64-bit TSC into EDX:EAX
    asm volatile("rdtsc" : "=a" (lo), "=d" (hi));
    return (unsigned long long)hi << 32 | lo;
}

std::atomic<bool> g_start(false);
std::atomic<unsigned int> totalTime(0);

template<typename Method>
void measureFunc(Method method)
{
    // warmup
    for (unsigned int i = 0; i < NUM_SAMPLES; i++)
    {
        method();
    }

    auto start = std::chrono::system_clock::now();

    for (unsigned int i = 0; i < NUM_SAMPLES; i++)
    {
        method();
    }

    auto end = std::chrono::system_clock::now();
    totalTime += std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
}

template<typename Method>
void measureThread(Method method)
{
    while(!g_start.load());

    measureFunc(method);
}

template<typename Method>
void measure(const std::string& methodName, Method method)
{
    std::vector<std::thread> threads;

    totalTime.store(0);
    g_start.store(false);

    for (unsigned int i = 0; i < NUM_THREADS; i++)
    {
        threads.push_back(std::thread(measureThread<Method>, method));
    }

    g_start.store(true);

    for (std::thread& th : threads)
    {
        th.join();
    }

    double timePerThread = (double)totalTime / (double)NUM_THREADS;
    double qps = NUM_SAMPLES / (double)totalTime;

    std::cout << timePerThread << "ms per thread" << "<<<<" << methodName << std::endl;
    std::cout << qps << " qps" << "<<<<" << methodName << std::endl;
}

int main(int argc, char** argv)
{
    NUM_THREADS = 1;
    measure("rdtsc", [](){ return gettsc(); });
    measure("gettimeofday", [](){ timeval tv; return gettimeofday(&tv, 0); });
    measure("time", [](){ return time(NULL); });
    measure("std chrono system_clock", [](){ return std::chrono::system_clock::now(); });
    measure("std chrono steady_clock", [](){ return std::chrono::steady_clock::now(); });
    measure("clock_gettime monotonic", [](){ timespec tp; return clock_gettime(CLOCK_MONOTONIC, &tp); });
    measure("clock_gettime cpu time", [](){ timespec tp; return clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &tp); });

    std::cout << "\n======\n";

    NUM_THREADS = 100;
    measure("rdtsc", [](){ return gettsc(); });
    measure("gettimeofday", [](){ timeval tv; return gettimeofday(&tv, 0); });
    measure("time", [](){ return time(NULL); });
    measure("std chrono system_clock", [](){ return std::chrono::system_clock::now(); });
    measure("std chrono steady_clock", [](){ return std::chrono::steady_clock::now(); });
    measure("clock_gettime monotonic", [](){ timespec tp; return clock_gettime(CLOCK_MONOTONIC, &tp); });
    measure("clock_gettime cpu time", [](){ timespec tp; return clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &tp); });

    return 0;
}
