#include "threadPool.hpp"
#include "assert.h"
#include <iostream>
#include <thread>

int main()
{
    ThreadPool pool(std::thread::hardware_concurrency());
    for (int i = 0; i < 20; ++i) {
        pool.addTask(i);
    }
    //while(1){};
    sleep(1); // wait for threads in thread pool to finish execution
    pool.shutdown();
    sleep(1); // wait shutdown
    return 0;
}
