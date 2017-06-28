#include "RAII.hpp"

int main()
{
    SmartPtr<int> ptr(new int());
    *ptr = 20;
    cout << *ptr << endl;

    // We don't need to call delete ptr: when the object ptr
    // goes out of scope, destructor for it is automatically
    // called and destructor does delete ptr.

    return 0;
}
