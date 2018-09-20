#include <thread>
#include <mutex>
#include <iostream>
#include <chrono>
#include <pthread.h>

using namespace std;

mutex m1, m2;


void task1() {
    unique_lock<mutex> lock1(m1);
    // set meaningful thread name
    //pthread_setname_np(pthread_self(), "dead lock task1");
    cout << "thread " <<  this_thread::get_id() << " acquired lock 1" << endl;

    std::this_thread::sleep_for(chrono::milliseconds(2));
    unique_lock<mutex> lock2(m2);
    cout << "thread " <<  this_thread::get_id() << " acquired lock 2" << endl;
}

void task2() {
    unique_lock<mutex> lock2(m2);
    // set meaningful thread name
    //pthread_setname_np(pthread_self(), "dead lock task2");
    cout << "thread " <<  this_thread::get_id() << " acquired lock 2" << endl;

    std::this_thread::sleep_for(chrono::milliseconds(2));
    unique_lock<mutex> lock1(m1);
    cout << "thread " <<  this_thread::get_id() << " acquired lock 1" << endl;
}

void deadlock() {
    thread t1(task1);
    thread t2(task2);

    // set thread name
    pthread_setname_np(t1.native_handle(), "dead lock task1"); // name length restricted to 16 characters
    pthread_setname_np(t2.native_handle(), "dead lock task2");
    //pthread_setname_np(t1.get_id(), "dead lock task1");
    t1.join();
    t2.join();
}

int main(int argc, char *argv[])
{
    deadlock();
    return 0;
}
