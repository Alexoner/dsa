#include <memory>
#include <iostream>
#include <mutex>

using namespace std;

class A {
public:
    A() {};
    int v;
    mutex lock;
    //mutex lock();
    //int v = 0;
};

int test() {
    shared_ptr<A> pa = make_shared<A>();
    cout << pa->v << endl;
    return 0;
}

int main() {
    return test();
}
