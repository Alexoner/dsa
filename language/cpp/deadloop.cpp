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
