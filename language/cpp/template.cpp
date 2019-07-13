#include <debug.hpp>
#include <iostream>
#include <memory>
#include <thread>
#include <chrono>

template<typename InputType, typename ResultType>
class A
{
public:
    virtual void say(InputType input) {};
};


class B: public A<string, int>
{
    virtual void say(string input);
};

class Traits
{
public:
    typedef int Type;
};

// template class
template<class T>
class Base
{
public:
    virtual typename T::Type foo()
    {
        cout << "hello, foo: " << endl;
    }
};

void B::say(string input)
{
    cout << "input is: " << input << endl;
}

// inherit a specialized template class
class C: public Base<Traits>
//class C: public Base<C> curiously recurring template pattern
{
public:
    typedef int Type;

    int bar()
    {
        cout << "hello, bar" << endl;
        return 0;
    }
};


int main(int argc, char *argv[])
{
    //A a;
    //a.say(string("hello world"));
    A<string, int> *pa = new B();
    pa->say(string("hello world"));
    //a.say(123);

    //Base<Traits> c;
    C c;
    c.foo();
    //c.bar();

    return 0;
}
