#include "threadPool.hpp"
#include "assert.h"
#include <iostream>

int main()
{
    ThreadPool pool(3);
    for (int i = 0; i < 20; ++i) {
        pool.addTask(i);
    }
    //while(1){};
    sleep(1);
    pool.shutdown();
    sleep(1);
    return 0;
}
