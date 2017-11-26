#include <functional>
#include <iostream>
#include <assert.h>

void testRecursive() {
    //std::function<int(int)> factorial = NULL;
    //std::function<int(int)> factorial = [&](int n) {
    std::function<int(int)> factorial = [&](int n) -> int {
        if (n <= 1) {
            return 1;
        }
        return factorial(n - 1) * n;
    };

    assert (factorial(0) == 1);
    assert (factorial(1) == 1);
    assert (factorial(2) == 2);
    assert (factorial(5) == 120);
    assert (factorial(10) == 3628800);
}

int main() {

    testRecursive();

    std::cout << "self test passed!" << std::endl;
    return 0;

}
