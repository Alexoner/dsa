#include <thread>
#include <mutex>
#include <iostream>
#include <chrono>

using namespace std;

mutex m1, m2;


void task1() {
    unique_lock<mutex> lock1(m1);
    cout << "thread " <<  this_thread::get_id() << " acquired lock 1" << endl;

    std::this_thread::sleep_for(chrono::milliseconds(2));
    unique_lock<mutex> lock2(m2);
    cout << "thread " <<  this_thread::get_id() << " acquired lock 2" << endl;
}

void task2() {
    unique_lock<mutex> lock2(m2);
    cout << "thread " <<  this_thread::get_id() << " acquired lock 2" << endl;

    std::this_thread::sleep_for(chrono::milliseconds(2));
    unique_lock<mutex> lock1(m1);
    cout << "thread " <<  this_thread::get_id() << " acquired lock 1" << endl;
}

void deadlock() {
    thread t1(task1);
    thread t2(task2);
    t1.join();
    t2.join();
}

int main(int argc, char *argv[])
{
    deadlock();
    return 0;
}
