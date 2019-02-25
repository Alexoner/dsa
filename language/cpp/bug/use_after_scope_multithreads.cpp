/**
 * Compile:
 * $ clang -std=c++11 -O -g -fsanitize=address -fsanitize-address-use-after-scope use_after_scope_multithreads.cpp
 *
 * Run:
 * $ ./a.out
 *
 */
#include <thread>
#include <debug.hpp>

struct Callable {
    int& i; // dangerous reference variable usage in detached thread mode

    Callable(int& i_): i(i_) {}

    void operator() (int step=1) {
        try {
            for (unsigned j = 0; j < 1000000; ++j) {
                i += step; // FIXME: potential access to dangling reference in detached thread! segmentation fault
            }
            cout << "callable finished with i: " << i << endl;

        } catch (exception e) {
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
    std::unique_ptr<thread> pThread;
    {
        int i = 0;
        Callable callable(i);
        pThread.reset(new thread(callable, 2));
    }

    thread &t = *pThread;
    thread_guard tg(t);
    //thread_guard tg1 = tg; // call to deleted constructor
    thread_guard& tg2 = tg;

    // do something in current thread
    for(int i = 0; i < 1000; ++i);
    cout << "current thread" << " '" << std::this_thread::get_id() << "' " << " task finished" << endl;
    if (t.joinable()) {
        // FIXME: running out of this function scope causes dangling reference to `i`.
        //t.detach(); // detach immediately after new thread executes
        t.join(); // can't join detached thread
    }
}

int main(int argc, char *argv[])
{
    f();
    return 0;
}

/**
 * Expect:
 *=================================================================
current thread '139841237243776'  task finished
==29820==ERROR: AddressSanitizer: stack-use-after-scope on address 0x7ffc373f1950 at pc 0x000000405e22 bp 0x7f2f4e4fec30 sp 0x7f2f4e4fec28
WRITE of size 4 at 0x7ffc373f1950 thread T1
    #0 0x405e21 in Callable::operator()(int) /home/hao.du/Documents/mine/dsa/language/cpp/bug/use_after_scope_multithreads.cpp:20
    #1 0x406c59 in void std::__invoke_impl<void, Callable, int>(std::__invoke_other, Callable&&, int&&) /home/hao.du/.linuxbrew/Cellar/gcc@8/8.2.0/include/c++/8.2.0/bits/invoke.h:60
    #2 0x406585 in std::__invoke_result<Callable, int>::type std::__invoke<Callable, int>(Callable&&, int&&) /home/hao.du/.linuxbrew/Cellar/gcc@8/8.2.0/include/c++/8.2.0/bits/invoke.h:95
    #3 0x40778c in decltype (__invoke((_S_declval<0ul>)(), (_S_declval<1ul>)())) std::thread::_Invoker<std::tuple<Callable, int> >::_M_invoke<0ul, 1ul>(std::_Index_tuple<0ul, 1ul>) /home/hao.du/.linuxbrew/Cellar/gcc@8/8.2.0/include/c++/8.2.0/thread:234
    #4 0x4076ff in std::thread::_Invoker<std::tuple<Callable, int> >::operator()() /home/hao.du/.linuxbrew/Cellar/gcc@8/8.2.0/include/c++/8.2.0/thread:243
    #5 0x407677 in std::thread::_State_impl<std::thread::_Invoker<std::tuple<Callable, int> > >::_M_run() /home/hao.du/.linuxbrew/Cellar/gcc@8/8.2.0/include/c++/8.2.0/thread:186
    #6 0x7f2f51fcbbce  (/home/hao.du/.linuxbrew/lib/gcc/8/libstdc++.so.6+0xbabce)
    #7 0x7f2f517db6b9 in start_thread (/lib/x86_64-linux-gnu/libpthread.so.0+0x76b9)
    #8 0x7f2f5151141c in clone (/lib/x86_64-linux-gnu/libc.so.6+0x10741c)

Address 0x7ffc373f1950 is located in stack of thread T0 at offset 32 in frame
    #0 0x4051fd in f() /home/hao.du/Documents/mine/dsa/language/cpp/bug/use_after_scope_multithreads.cpp:51

  This frame has 5 object(s):
    [32, 36) 'i' <== Memory access at offset 32 is inside this variable
    [96, 100) '<unknown>'
    [160, 168) 'pThread'
    [224, 232) 'callable'
    [288, 296) 'tg'
HINT: this may be a false positive if your program uses some custom stack unwind mechanism or swapcontext
      (longjmp and C++ exceptions *are* supported)
SUMMARY: AddressSanitizer: stack-use-after-scope /home/hao.du/Documents/mine/dsa/language/cpp/bug/use_after_scope_multithreads.cpp:20 in Callable::operator()(int)
Shadow bytes around the buggy address:
  0x100006e762d0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x100006e762e0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x100006e762f0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x100006e76300: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x100006e76310: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
=>0x100006e76320: 00 00 00 00 00 00 f1 f1 f1 f1[f8]f2 f2 f2 f2 f2
  0x100006e76330: f2 f2 f8 f2 f2 f2 f2 f2 f2 f2 00 f2 f2 f2 f2 f2
  0x100006e76340: f2 f2 f8 f2 f2 f2 f2 f2 f2 f2 00 f2 f2 f2 f3 f3
  0x100006e76350: f3 f3 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x100006e76360: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x100006e76370: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
Shadow byte legend (one shadow byte represents 8 application bytes):
  Addressable:           00
  Partially addressable: 01 02 03 04 05 06 07
  Heap left redzone:       fa
  Freed heap region:       fd
  Stack left redzone:      f1
  Stack mid redzone:       f2
  Stack right redzone:     f3
  Stack after return:      f5
  Stack use after scope:   f8
  Global redzone:          f9
  Global init order:       f6
  Poisoned by user:        f7
  Container overflow:      fc
  Array cookie:            ac
  Intra object redzone:    bb
  ASan internal:           fe
  Left alloca redzone:     ca
  Right alloca redzone:    cb
Thread T1 created by T0 here:
    #0 0x7f2f522dc400 in pthread_create (/home/hao.du/.linuxbrew/lib/gcc/8/libasan.so.5+0x49400)
    #1 0x7f2f51fcbe54 in std::thread::_M_start_thread(std::unique_ptr<std::thread::_State, std::default_delete<std::thread::_State> >, void (*)()) (/home/hao.du/.linuxbrew/lib/gcc/8/libstdc++.so.6+0xbae54)
    #2 0x4053ba in f() /home/hao.du/Documents/mine/dsa/language/cpp/bug/use_after_scope_multithreads.cpp:56
    #3 0x405658 in main /home/hao.du/Documents/mine/dsa/language/cpp/bug/use_after_scope_multithreads.cpp:76
    #4 0x7f2f5142a82f in __libc_start_main (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

==29820==ABORTING
[1]    29820 abort (core dumped)  ./bin/use_after_scope_multithreads±
 */
