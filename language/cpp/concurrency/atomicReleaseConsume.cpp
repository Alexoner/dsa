#include <thread>
#include <atomic>
#include <cassert>
#include <string>
#include <iostream>

std::atomic<std::string*> ptr;
std::atomic<bool> flag(false);
int data = 0;

void producer()
{
    while(true)
    {
        while (!flag.load());
        std::string* p  = new std::string("Hello");
        data = 42;
        ptr.store(p, std::memory_order_release);
        //ptr.store(p, std::memory_order_relaxed);
    }
}

void consumer()
{
    while (true)
    {
        while (!flag.load());
        std::string* p2;
        while (!(p2 = ptr.load(std::memory_order_consume)))
        //while (!(p2 = ptr.load(std::memory_order_relaxed)))
            ;
        assert(data == 42); // may or may not fire: data does not carry dependency from ptr
        assert(*p2 == "Hello"); // never fires: *p2 carries dependency from ptr
        std::cout << "passed" << std::endl;
    }
}

int main()
{
    std::thread t2(consumer);
    std::thread t1(producer);
    for (int i = 0;; ++i)
    {
        flag.store(true);
        std::this_thread::sleep_for(std::chrono::microseconds(10));
        flag.store(false);
        std::this_thread::sleep_for(std::chrono::microseconds(100));
        data = 0;
    }
    t1.join(); t2.join();
}
