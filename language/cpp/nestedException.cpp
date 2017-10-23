/*
 * Source: https://www.toptal.com/c-plus-plus/interview-questions
 *
What is the output of the following code:

Answer:
 *
 * This program will terminate abnormally. throw 32 will start unwinding the stack and destroy class A. The class A destructor will throw another exception during the exception handling, which will cause program to crash. This question is testing if developer has experience working with exceptions.
 *
 */
#include <iostream>

class A {
public:
    A() {}
    ~A() {
        throw 42;
    }
};

int main(int argc, const char * argv[]) {
    try {
        A a;
        throw 32;
    } catch(int a) {
        std::cout << a;
    }
}
