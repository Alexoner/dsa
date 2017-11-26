#include <iostream>
#include <stdint.h>
#include <assert.h>

#include <functional>
#include <vector>
#include <map>
#include <stack>
#include <queue>
#include <algorithm>
#include <sstream>
#include <numeric>

using namespace std;

template <typename T>
string to_string(vector<T> v)
{
    return std::accumulate(
           v.begin(),
           v.end(),
           string("{"),
           [](string a, char b) {
           return a + std::to_string(b) + ", ";
           })
    + string("}");
}

template <typename T>
string to_string(stack<T> v)
{
    return std::accumulate(
           v.begin(),
           v.end(),
           string("{"),
           [](string a, char b) {
           return a + std::to_string(b) + ", ";
           })
    + string("}");
}

template <typename T>
string to_string(queue<T> v)
{
    return std::accumulate(
           v.begin(),
           v.end(),
           string("{"),
           [](string a, char b) {
           return a + std::to_string(b) + ", ";
           })
    + string("}");
}

//  Windows
#ifdef _WIN32

#include <intrin.h>
uint64_t rdtsc(){
    return __rdtsc();
}

//  Linux/GCC
#else

uint64_t rdtsc(){
    unsigned int lo,hi;
    __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
    return ((uint64_t)hi << 32) | lo;
}

#endif
