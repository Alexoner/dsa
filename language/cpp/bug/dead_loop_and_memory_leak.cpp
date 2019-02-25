/**
 *
 * run:
 * $ LD_PRELOAD=/usr/lib/x86_64-linux-gnu/liblsan.so.0 ./bin/dead_loop_and_memory_leak
 * $ ctrl+c
 *
 *=================================================================
==9662==ERROR: LeakSanitizer: detected memory leaks

Direct leak of 110592 byte(s) in 108 object(s) allocated from:
    #0 0x7f42145c1975 in operator new[](unsigned long) (/usr/lib/x86_64-linux-gnu/liblsan.so.0+0xd975)
    #1 0x404d5f in main /home/hao.du/Documents/mine/dsa/language/cpp/bug/dead_loop_and_memory_leak.cpp:51
    #2 0x7f4213a5582f in __libc_start_main (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

Direct leak of 109568 byte(s) in 107 object(s) allocated from:
    #0 0x7f42145c1975 in operator new[](unsigned long) (/usr/lib/x86_64-linux-gnu/liblsan.so.0+0xd975)
    #1 0x404d49 in main /home/hao.du/Documents/mine/dsa/language/cpp/bug/dead_loop_and_memory_leak.cpp:49
    #2 0x7f4213a5582f in __libc_start_main (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

SUMMARY: LeakSanitizer: 220160 byte(s) leaked in 215 allocation(s).
 */
#include <iostream>
#include <thread>
#include <chrono>
#include <csignal>
#include <memory>
//#include <sanitizer/lsan_interface.h>

using namespace std;

/*
 * Example program to debug where a running program is stuck
 *
 */

const int _1B = 1;
const int _1K = 1024;
const int _1M = _1K * _1K;
const int _1G = _1M * _1M;
const std::string SPIN = "-\\|/";

volatile std::sig_atomic_t gSignalStatus;
bool shouldRun = true;

class A {
    public:
        string name = "A";
};

void signal_handler(int signal)
{
    std::cout << "handle signal " << signal << std::endl;
    shouldRun = false;
}

int main(int argc, char *argv[])
{
    // install a signal handler
    // handle a signal to exit the infinite loop and run main return, to enable address sanitizer report
    std::signal(SIGINT, signal_handler);

    int i = 0;
    char *p = NULL;
    std::cout << "running a problematic program with dead loop and memory leak ^_^" << std::endl;
    while (shouldRun) { // dead loop forever
        i += 1;
        p = new char[_1K];
        p = NULL; // causes memory leak
        p = new char[_1K];
        shared_ptr<A> pa = make_shared<A>();
        std::this_thread::sleep_for(std::chrono::milliseconds(10));

        std::cout << "continuing: " << SPIN[i % 4] << "\r";
        std::flush(std::cout);
        //__lsan_do_leak_check(); // FIXME: doesn't work, how to use it?
    };
    return 0;
}
