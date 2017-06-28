#include "threadPool.hpp"

void* workerLoop(void* data)
{
    printf("starting runLoop, data: %p\n", data);
    //cout << "hello from runLoop, data: " << data << endl;
    ThreadPool* ptr = (ThreadPool*)data;
    ptr->runLoop();

    return NULL;
}
