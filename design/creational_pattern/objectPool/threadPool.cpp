#include "threadPool.hpp"

void* runLoop(void* data)
{
    printf("starting runLoop, data: %p\n", data);
    //cout << "hello from runLoop, data: " << data << endl;
    ThreadPool* ptr = (ThreadPool*)data;
    ptr->workerLoop();

    return NULL;
}
