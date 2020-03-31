#include <debug.hpp>
#include <iostream>
#include <memory>
#include <thread>
#include <chrono>


class Base
{
public:
    typedef int Input;

public:
    virtual void process(Input input)
    {
        cout << "input is: " << input << endl;
    }

};

class Derived
{
public:
    typedef string Input;

public:
    virtual void process(string input)
    {
        cout << "input is: " << input << endl;
    }

};

int main(int argc, char *argv[])
{
    shared_ptr<Base> pBase(new Base());
    pBase->process(123);

    unsigned int a = 2;
    int b = -1;

    if (a > b)
    {
        cout << a << " > " << b;
    }

    //pBase.reset(new Derived());
    //pBase->process(string("hello world"));

    return 0;
}
