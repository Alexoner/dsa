#include <debug.hpp>
#include <atomic>
#include <thread>

atomic<bool> flag(false); // signal begin

int gTestCount = 10000;

void test_memory_order_sequential_consistent() {
    cout << "TESTING memory order sequential consistent" << endl;
    auto t0 = std::chrono::steady_clock::now();
    atomic<int> x(0), y(0);
    int r1, r2;

    int i = 0;
    while(++i < gTestCount) {
        x.store(0);
        y.store(0);
        r1 = r2 = 0;

        thread t1([&]() {
                x.store(1);
                r1 = y.load();
                });
        thread t2([&]() {
                y.store(1);
                r2 = x.load();
                });
        t1.join();
        t2.join();

        assert(!(r1 == 0 && r2 == 0));
    }

    auto t1 = std::chrono::steady_clock::now();

    cout << "memory order sequential consistent passed within "
        << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count()
        << endl;
}

void test_memory_order_relaxed() {
    cout << "TESTING memory order relaxed" << endl;
    auto t0 = std::chrono::steady_clock::now();

    atomic<int> x(0), y(0);
    int r1, r2;

    int i = 0;
    while(++i < gTestCount * 10)  {
        x = y = 0;
        r1 = r2 = 0;
        thread t1([&] {
                //while(!flag.load(memory_order_relaxed));
                //relaxed operations on separate variables might be reordered by compiler or hardware
                x.store(1, memory_order_relaxed);
                r1 = y.load(memory_order_relaxed);
                });
        thread t2([&](void) -> void {
                //while(!flag.load(memory_order_relaxed));
                y.store(1, memory_order_relaxed);
                r2 = x.load(memory_order_relaxed);
                });

        flag.store(true);
        t1.join();
        t2.join();

        if (r1 == 0 && r2 == 0) {
            cout << "MEMORY REORDER detected!" << " iteration: " << i << endl;
            break;
        };
    }
    auto t1 = std::chrono::steady_clock::now();
    cout << "memory order relaxed passed within "
        << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count()
        << endl;
}

/**
 * demonstrates transitive release-acquire ordering across three threads
 */
void test_memory_order_release_acquire() {
    cout << "TESTING memory order release and acquire" << endl;
    auto t0 = std::chrono::steady_clock::now();

    atomic<int> x(0), y(0);

    int i = 0;
    while(++i < gTestCount)  {
        std::vector<int> data;
        std::atomic<int> flag = {0};
        auto thread_1 = [&]()
        {
            data.push_back(42);
            flag.store(1, std::memory_order_release);
        };

        auto thread_2 = [&]()
        {
            int expected=1;
            while (!flag.compare_exchange_strong(expected, 2, std::memory_order_acq_rel)) {
                expected = 1;
            }
        };

        auto thread_3 = [&]()
        {
            while (flag.load(std::memory_order_acquire) < 2)
                ;
            assert(data.at(0) == 42); // will never fire
        };

        std::thread a(thread_1);
        std::thread b(thread_2);
        std::thread c(thread_3);
        a.join(); b.join(); c.join();
    }

    auto t1 = std::chrono::steady_clock::now();
    cout << "memory order release acquire passed within "
        << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count()
        << endl;

}

//https://preshing.com/20140709/the-purpose-of-memory_order_consume-in-cpp11/
void test_memory_order_release_consume() {
    cout << "TESTING memory order release and consume" << endl;
    auto t0 = std::chrono::steady_clock::now();

    atomic<int*> x(0);
    int r1, r2;

    int i = 0;
    while(++i < gTestCount)  {
        x = 0;
        r1 = r2 = 0;

        thread t1([&] {
                r1 = 1;
                r2 = 1;
                x.store(&r1, memory_order_release); // producer
                });
        thread t2([&]() {
                int *t = x.load(memory_order_acquire);
                if (t) assert(*t == 1 && r2 == 1); // will pass
                });
        thread t3([&]() {
                int *t = x.load(memory_order_consume); // consumer
                if (t) assert(*t == 1 && r2 == 1); // can fail because there is no longer a dependency between the store to x, and the store to r2, and therefore the values do not need to be synchronized. This models the PowerPC and ARM's default memory ordering for pointer loads. (and possibly some MIPs targets)
                if (r1 == 1 && r2 == 0) {
                    // supposed to fire sometimes, if and only if compile and CPU supports such memory order, otherwise may treated as release-acquire.
                    cout << "MEMORY REORDER detected!" << " iteration: " << i << endl;
                };
            });


        t1.join();
        t2.join();
        t3.join();

    }
    auto t1 = std::chrono::steady_clock::now();

    cout << "memory order release acquire passed within "
        << std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count()
        << endl;

}


void test_fences() {
    cout << "TESTING fence" << endl;

    atomic<int> x(0), y(0);
    int r1, r2;

    int i = 0;
    // TODO: fences don't work yet?
    while(++i < gTestCount)  {
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
                //cout << "r1: " << r1 << " r2: " << r2 << endl;
                });
        t1.join();
        t2.join();

        if (r1 == 0 && r2 == 0) {
            cout << "MEMORY REORDER detected!" << " iteration: " << i << endl;
            break;
        };
        //assert(!(r1 == 0 && r2 == 0)); // should it fire?
    }
}

// TODO: ABA problem in lock free algorithm

int main(int argc, char *argv[])
{
    atomic<void*> aPointer;

    cout << "atomic<>::is_lock_free(): " << aPointer.is_lock_free() << endl;

    int i = 0;
    test_memory_order_sequential_consistent();
    test_memory_order_relaxed();
    test_memory_order_release_acquire();
    test_memory_order_release_consume();

    test_fences();

    return 0;
}
