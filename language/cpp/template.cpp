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

void B::say(string input)
{
    cout << "input is: " << input << endl;
}


int main(int argc, char *argv[])
{
    //A a;
    //a.say(string("hello world"));
    A<string, int> *pa = new B();
    pa->say(string("hello world"));
    //a.say(123);
    return 0;
}
