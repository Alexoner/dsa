/**
 *
 * Demonstrate SIMID intrinsic for array sum function.
 *
 *
 * GCC optimize options:
 * https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html
 *
 * g++ -std=c++11 -O2 sum.cpp
 *
 *
 * Reference:
 * https://stackoverflow.com/questions/11872952/simd-the-following-code
 * https://www.cs.virginia.edu/~cr4bd/3330/F2018/simdref.html
 *
 */
#include <iostream>
#include <vector>
#include <chrono>
#include <thread>
#include <emmintrin.h>

using namespace std;

template <class Func>
float timeit(Func func, std::string name)
{
    auto start = std::chrono::system_clock::now();
    func();
    //std::this_thread::sleep_for(std::chrono::seconds(1));
    auto end = std::chrono::system_clock::now();
    float timeElapsed = std::chrono::duration_cast<std::chrono::microseconds>(end-start).count();
    cout << "function " << name << " used time: " << timeElapsed << endl;
}

// to enable compiler loop unrolling, use following two method
//__attribute__((optimize("unroll-loops")))

//#pragma GCC push_options
//#pragma GCC optimize ("unroll-loops")
int sum0(int *arr, int n)
{
    int x = 0;
    for (int i = 0; i < n; ++i) {
        x += arr[i];
    }
    return x;
}
//#pragma GCC pop_options

int sumLoopUnrolled(int *arr, int n)
{
    int x = 0;
    int a = 0, b = 0, c = 0;
    for (int i = 0; i < n; i += 4) {
        x += arr[i];
        a += arr[i+1];
        b += arr[i+2];
        c += arr[i+3];
    }
    x += a;
    x += b;
    x += c;
    return x;
}

int sumIntrinsic(int32_t *arr, int n)
{
    __m128i vsum = _mm_set1_epi32(0);           // initialise vector of four partial 32 bit sums
    uint32_t sum;

    int i;
    for (i = 0; i < n; i += 4)
    {
        __m128i v = _mm_load_si128((__m128i*)&arr[i]);      // load vector of 4x32 bit values
        vsum = _mm_add_epi32(vsum, v); // accumulate to 32 bit partial sum vector

        // XXX: does this work too?
        //vsum = _mm_add_epi32(vsum, *(__m128i*)(arr + i));
    }
    // horizontal add of four 32 bit partial sums and return result
    vsum = _mm_add_epi32(vsum, _mm_srli_si128(vsum, 8)); // shift right by 8 bytes=64 bits
    vsum = _mm_add_epi32(vsum, _mm_srli_si128(vsum, 4));
    sum = _mm_cvtsi128_si32(vsum);
    return sum;
}

int test() {
    int n = 4 * 100000000;
    vector<int> arr(n, 1);
    for (int i = 0; i < n; ++i) {
        arr[i] = i % 4;
    }
    int c = 0;

    c = 0;
    timeit([&arr, &n, &c]() {
            int i = n;
            //while (i--)
            c += sum0(arr.data(), n);
            }, "trivial sum");

    cout << "c: " << c << endl;

    c = 0;
    timeit([&arr, &n, &c]() {
            int i = n;
            //while (i--)
            c += sumLoopUnrolled(arr.data(), n);
            }, "sum loop unrolled");
    cout << "c: " << c << endl;

    c = 0;
    timeit([&arr, &n, &c]() {
            int i = n;
            //while (i--)
            c += sumIntrinsic(arr.data(), n);
            }, "sum loop intrinsic");
    cout << "c: " << c << endl;


    return 0;
}


int main(int argc, char *argv[])
{
    test();

    return 0;
}
