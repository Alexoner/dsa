#include <debug.hpp>
#include <atomic>
#include <thread>

atomic<int> x(0), y(0);
atomic<int> z;

int r1, r2;

void thread1() {
    x.store(1);
    r1 = y.load();
}

void thread2() {
    y.store(1);
    r2 = x.load();
}

void test_memory_order_sequential_consistent() {
    cout << "TESTING memory order sequential consistent" << endl;
    int i = 0;
    while(++i < 1000) {
        x.store(0);
        y.store(0);
        r1 = r2 = 0;

        thread t1([&]() {
                x.store(1);
                r1 = y.load();
                });
        //thread t2(thread2);
        thread t2([&]() {
                y.store(1);
                r2 = x.load();
                });
        t1.join();
        t2.join();

        assert(!(r1 == 0 && r2 == 0));
    }
    cout << "memory order sequential consistent passed!" << endl;
}

void test_memory_order_relaxed() {
    cout << "TESTING memory order relaxed" << endl;
    int i = 0;
    while(++i < 10000)  {
        x = y = false;
        r1 = r2 = 0;
        thread t1([&] {
                //relaxed operations on separate variables might be reordered by compiler or hardware
                x.store(1, memory_order_relaxed);
                r1 = y.load(memory_order_relaxed);
                });
        thread t2([&](void) -> void {
                y.store(1, memory_order_relaxed);
                r2 = x.load(memory_order_relaxed);
                });
        t1.join();
        t2.join();

        if (r1 == 0 && r2 == 0) {
            cout << "memory reorder detected!" << " iteration: " << i << endl;
        };
    }
}

void test_fences() {
    cout << "TESTING fence" << endl;
    int i = 0;
    // TODO: fences don't work yet?
    while(++i < 10000)  {
        x = y = false;
        r1 = r2 = 0;
        thread t1([&] {
                x.store(1, memory_order_relaxed);
                atomic_thread_fence(memory_order_release);
                r1 = y.load(memory_order_relaxed);
                });
        thread t2([&](void) -> void {
                y.store(1, memory_order_relaxed);
                atomic_thread_fence(memory_order_acquire);
                r2 = x.load(memory_order_relaxed);
                cout << "r1: " << r1 << " r2: " << r2 << endl;
                });
        t1.join();
        t2.join();

        if (r1 == 0 && r2 == 0) {
            cout << "memory reorder detected!" << " iteration: " << i << endl;
        };
        assert(!(r1 == 0 && r2 == 0));
    }
}

void test_lock_free() {

}

// TODO: ABA problem in lock free algorithm

int main(int argc, char *argv[])
{
    void *p;
    atomic<void*> aPointer;

    cout << "atomic<>::is_lock_free(): " << aPointer.is_lock_free() << endl;

    int i = 0;
    test_memory_order_sequential_consistent();

    test_memory_order_relaxed();
    test_fences();

    return 0;
}
