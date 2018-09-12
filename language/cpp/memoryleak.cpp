//#include <debug.hpp>
#include <iostream>
#include <thread>
#include <chrono>
//#include <sanitizer/lsan_interface.h>


char* leak()
{
    std::cout << "leaking" << std::endl;
    char *p = NULL;
    for (int i = 0; i < 10; ++i) {
        std::cout << "leaking: " << i << std::endl;
        p = new char[1024];
        p = NULL;
    }

    std::cout << "leaking done" << std::endl;

    return p;
}

bool exit_thread = false;

void threadFunc()
{
   while(!exit_thread)
   {
      char* pLeak = new char[256];
      std::this_thread::sleep_for(std::chrono::seconds{1});
   }
}

int main() {
   char *p = leak();
   //p[0] = 0;

   //std::thread t(threadFunc);
   //std::cout << "Waiting\n";
   //std::this_thread::sleep_for(std::chrono::seconds{2});
   //exit_thread = true;
   //std::cout << "Exiting\n";
   //Without joining here I do not get the leak report.
   //t.join();
   //__lsan_do_recoverable_leak_check();

   //std::this_thread::sleep_for(std::chrono::seconds{5});
   std::cout << "Done\n";

   return 0;
}
