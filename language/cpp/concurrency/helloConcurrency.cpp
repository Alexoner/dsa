#include <thread>
#include <debug.hpp>


void hello() {
    cout << "Hello, concurrent world!" << endl;
}

int main(int argc, char *argv[])
{
    thread t(hello);
    t.join();

    return 0;
}
