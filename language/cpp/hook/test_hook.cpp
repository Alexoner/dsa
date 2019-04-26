#include <iostream>
#include <memory.h>
#include "debug.hpp"

//#include <easylogging++.h>
//INITIALIZE_EASYLOGGINGPP


int main(int argc, char *argv[])
{
    vector<int> a(1000, 9);
    vector<int> b(1000);
    std::cout << "a.size(): " << a.size() << endl;
    memcpy(b.data(), a.data(), sizeof(int) * a.size());
    //std::cout << "hello world" << std::endl;
    //std::cout << b;
    return 0;
}
