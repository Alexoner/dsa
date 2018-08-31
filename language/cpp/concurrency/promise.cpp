// promise example
#include <iostream>       // std::cout
#include <functional>     // std::ref
#include <thread>         // std::thread
#include <future>         // std::promise, std::future
#include <chrono>
#include <cassert>
#include <debug.hpp>

void print_int (std::future<int>& fut) {

  int x = fut.get();
  std::cout << "value: " << x << '\n';
}

void add(int x, std::promise<int> prom) {
  x += 1;
  std::cout << "value: " << x << '\n';
  std::this_thread::sleep_for(chrono::seconds(1));
  prom.set_value(x);  // fulfill promise
}

std::thread t;
std::future<int> asyncIncrement(int x) {
  std::promise<int> prom; // create promise

  auto r = prom.get_future();    // engagement with future
  // XXX: std::async will give sigsegv
  t = std::thread(add, x, std::move(prom)); // move future to new thread
  return r;
}

void testAsyncIncrement() {
  int x = 0;
  auto r = asyncIncrement(x);
  //r.wait();
  try {

    int y = r.get();
    assert(y == x + 1);
    t.join();
  }catch(exception e) {
    std::cout << "error: " << e.what();
  }
}

void testNaive() {
  std::promise<int> prom;                      // create promise

  std::future<int> fut = prom.get_future();    // engagement with future

  std::thread th1 (print_int, std::ref(fut));  // send future to new thread

  prom.set_value (10);                         // fulfill promise
                                               // (synchronizes with getting the future)
  th1.join();

}

int main ()
{
  testNaive();
  testAsyncIncrement();

  return 0;
}
