#include "threadPool.hpp"

void* runLoop(void* data)
{
	  printf("starting runLoop, data: %x\n", data);
    //cout << "hello from runLoop, data: " << data << endl;
	ThreadPool* ptr = (ThreadPool*)data;
	ptr->workerLoop();

    return NULL;
}

void *thr_func(void *data) {

  printf("hello from thr_func, data: %x\n", data);
  /* get mutex before modifying and printing shared_x */
  return NULL;
}
