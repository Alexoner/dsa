#include <iostream>

using namespace std;

// a generic smart pointer class
template <class T>
class SmartPtr {
    T* ptr; // actual pointer
public:
    // Constructor: Refer http://www.geeksforgeeks.org/g-fact-93/,
    explicit SmartPtr(T* p = NULL) { ptr = p; }

    // Destructor
    ~SmartPtr()
    {
        cout << "deleting allocated memory" << endl;
        delete (ptr);
    }

    // Overloading dereferencing operator
    T& operator*()
    {
        return *ptr;
    }

    // Overloading arrow operator so that members of T can be accessed
    // like a pointer (useful if T represents a class or struct or
    // union type)
    T* operator->()
    {
        return ptr;
    }
};
