/*
 * What's the problem of the following code?
 *
 * Answer:
 *
 * The behavior is undefined because A’s destructor is not virtual. From the spec:

( C++11 §5.3.5/3 ) if the static type of the object to be deleted is different from its dynamic type, the static type shall be a base class of the dynamic type of the object to be deleted and the static type shall have a virtual destructor or the behavior is undefined.
 */

#include <iostream>

class A {
public:
    A() {}
    ~A() { std::cout << "destroying A" << std::endl;} // should be called when declared as virtual function
    //virtual ~A() { std::cout << "destroying A" << std::endl;}
};

class B : public A {
public:
    B()
	: A()
    {
    }
    ~B() { std::cout << "destroying B" << std::endl;}
};

int main(void)
{
    A* a = new B();
    delete a;
}
