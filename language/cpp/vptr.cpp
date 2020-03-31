/*
 * What will be the output of the following program?
 *
 * Answer:
 * In the main function the instance of struct A is treated as an array of integer values. On 32-bit architectures the output will be 33, and on 64-bit architectures it will be 22. This is because there is virtual method f() in the struct which makes compiler insert a vptr pointer that points to vtable (a table of pointers to virtual functions of class or struct). On 32-bit architectures the vptr takes 4 bytes of the struct instance and the rest is the data array, so arr[2] represents access to second element of the data array, which holds value 33. On 64-bit architectures the vptr takes 8 bytes so arr[2] represents access to the first element of the data array, which holds 22.

This question is testing knowledge of virtual functions internals, and knowledge of C++11-specific syntax as well, because the constructor of A uses the extended initializer list of the C++11 standard.

Compiled with:

g++ question_vptr.cpp -m32 -std=c++11
g++ question_vptr.cpp -std=c++11
 */

#include <iostream>

class Base
{
    int data[2];

public:
    Base(int x, int y) : data{x, y} {}
    virtual void f() {};
    virtual ~Base() {}
};

class Derived: public Base {
public:
    Derived(): Base(0, 1) {}
    void f() {}
    virtual ~Derived() {};

};

int main(int argc, char **argv)
{
    Base a(22, 33);
    Base *pBase = new Derived();
    pBase->f();
    delete pBase;

    int *arr = (int *) &a;
    std::cout << arr[2] << std::endl;

    return 0;
}
