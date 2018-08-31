#include <functional>
#include <iostream>
#include <assert.h>
#include <debug.hpp>

void testRecursive() {
    //std::function<int(int)> factorial = NULL;
    //std::function<int(int)> factorial = [&](int n) {
    std::function<int(int)> factorial = [&factorial](int n) -> int {
        if (n <= 1) {
            return 1;
        }
        return factorial(n - 1) * n;
    };

    assert(factorial(0) == 1);
    assert(factorial(1) == 1);
    assert(factorial(2) == 2);
    assert(factorial(5) == 120);
    assert(factorial(10) == 3628800);
}

int bar(int) = delete;

int main() {

    function<int(int)> foo = NULL;
    try {
        foo(1);
    }catch(exception e) {
        cout << "ERROR: " << e.what();
    }
    function<int(int)> &fooRef = foo;
    cout << "function foo is NULL: " << (foo == NULL) << endl;
    //bar(3);
    foo = [](int) -> int {
        return 0;
    };
    cout << "function foo is NULL: " << (foo == NULL) << endl;
    foo(3);
    testRecursive();

    int c = 0;

    auto fRef = [&]() {
        c += 1; // 1
        cout << "c: " << c << endl;
        assert(c == 1);
    };


    fRef();
    //auto f = Function(c);

    auto fCopy = [=]() mutable {
        c += 1; // 2
        assert(c == 2);
        cout << "c: " << c << endl;
    };
    fCopy();

    std::cout << "self test passed!" << std::endl;
    return 0;

}
