/*
 *  Debug objects copying while using STL map.
 *
 *  Source: https://stackoverflow.com/questions/13880631/insert-elements-into-stdmap-without-extra-copying
 *
 *
 */
#include <map>
#include <string>
#include <iostream>
#include <stdio.h>
#include <stdarg.h>

//#include "../logger/easylogging++.h"
#include <easylogging++.h>
INITIALIZE_EASYLOGGINGPP

using namespace std;

// there is no way to get the variable number arguments length,
// which has to be indicated by named arguments, such as format in printf
//void Log(const char* format, ...)
//{
    //va_list argptr;
    //va_start(argptr, format);
    //vfprintf(stdout, format, argptr);
    //va_end(argptr);
//}

//#define LOG magic_log_function // Please don't mind this.

//
// ADVENTURES OF PROGO THE C++ PROGRAM
//

class element;
typedef std::map<int, element> map_t;

class element {
public:
    element(const std::string&);
    element(const element&);
    ~element();
    std::string name;
};
element::element(const std::string& arg)
    : name(arg)
{
    LOG(DEBUG) << "element " << arg << " constucted, " << this;
}
element::element(const element& other)
    : name(other.name)
{
    name += "-copy";
    LOG(DEBUG) << "element " << name << " copied, " << this;
}
element::~element()
{
    LOG(DEBUG) << "element " << name << " destructed, " << this;
}

int main(int argc, char **argv)
{
    map_t map1; element b1("b1");
    LOG(INFO) << " < Done construction.";
    LOG(INFO) << " < Making map 1.";
    // element gets copied twice: pair construction, map insert
    map1.insert(std::pair<int, element>(1, b1));
    LOG(ERROR) << " > Done making map 1.";
    LOG(ERROR) << " > Before returning from main()";
}
