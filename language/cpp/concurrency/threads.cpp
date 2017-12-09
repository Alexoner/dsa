#include <thread>
#include <debug.hpp>

struct Callable {
    int& i; // dangerous reference variable usage in detached thread mode

    Callable(int& i_): i(i_) {}

    void operator() (int step=1) {
        try {
            for (unsigned j = 0; j < 1000000; ++j) {
                 i += step; // potential access to dangling reference in detached thread! segmentation fault
            }
            cout << "callable finished with i: " << i << endl;

        }catch(exception e) {
            cout << "ERROR executing callable" << e.what() << endl;
        }
        //std::this_thread::sleep_for (std::chrono::seconds(1));
    }
};

// RAII to wait for thread to complete
class thread_guard
{
    thread& t;
    public:
    thread_guard(thread& t_): t(t_) {}

    ~thread_guard() {
        if (t.joinable()) {
            cout << "thread '" << t.get_id() << "' joinable" << endl;
            t.join();
        } else {
            cout << "thread '" << t.get_id() << "' not joinable" << endl;
        }
    }

    thread_guard(thread_guard const&) = delete; // delete copy constructor
    thread_guard& operator=(thread_guard const) =delete; // delete copy-assignment operator
};

void f() {
    int i = 0;
    Callable callable(i);

    thread t(callable, 2);
    thread_guard tg(t);
    //thread_guard tg1 = tg; // call to deleted constructor
    thread_guard& tg2 = tg;

    // do something in current thread
    for(int i = 0; i < 1000; ++i);
    cout << "current thread" << " '" << std::this_thread::get_id() << "' " << " task finished" << endl;
    if (t.joinable()) {
        t.detach(); // detach immediately after new thread executes
    }
    //t.join();
}

int main(int argc, char *argv[])
{
    f();
    return 0;
}
