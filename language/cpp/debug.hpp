#pragma once

#include <stdint.h>
#include <assert.h>

#include "base_headers.hpp"


/**
 *
 * print a vector
 *
 */
template<typename T>
static std::ostream& operator<<(std::ostream& os, const std::vector<T>& container)
{
    os << "vector{";
    for (auto& x : container)
    {
        if (std::is_same<T, string>::value) {
            os << '"' << x << '"' << ", "; // wrap string between ""
        } else if (std::is_same<T, char>::value) {
            os << "'" << x << "'" << ", "; // wrap char between ''
        } else {
            os << x << ", "; // numeric data, print directly
        }
    }
    os << "}";
    return os;
}

template<typename T>
static std::ostream& operator<<(std::ostream& os, const std::multiset<T>& container)
{
    os << "multiset{";
    for (auto& x : container)
    {
        if (std::is_same<T, string>::value) {
            os << '"' << x << '"' << ", "; // wrap string between ""
        } else if (std::is_same<T, char>::value) {
            os << "'" << x << "'" << ", "; // wrap string between ''
        } else {
            os << x << ", ";
        }
    }
    os << "}";
    return os;
}

template<typename T>
static std::ostream& operator<<(std::ostream& os, const std::set<T>& container)
{
    os << "set{";
    for (auto& x: container) {
        if (std::is_same<T, string>::value) {
            os << '"' << x << '"' << ", ";
        } else if (std::is_same<T, char>::value) {
            os << "'" << x << "'" << ", ";
        } else {
            os << x << ", ";
        }
    }
    os << "}";

    return os;
}

static string to_string(string s) {
    return "\"" + s + "\"";
}

template <typename T>
string to_string(vector<T> v)
{
    return std::accumulate(
           v.begin(),
           v.end(),
           string("{"),
           [](string a, T b) {
           return a + to_string(b) + ", ";
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
static uint64_t rdtsc(){
    return __rdtsc();
}

//  Linux/GCC
#else

static uint64_t rdtsc(){
    unsigned int lo,hi;
    __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
    return ((uint64_t)hi << 32) | lo;
}

#endif
