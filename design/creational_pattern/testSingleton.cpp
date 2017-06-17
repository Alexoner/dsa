#include "singleton.hpp"
#include "assert.h"
#include <iostream>
using namespace std;

int main() {
    Singleton &s1 = Singleton::getInstance();
    Singleton &s2 = Singleton::getInstance();

    assert (&s1 == &s2);
    cout << "self test passed" << endl;
}
