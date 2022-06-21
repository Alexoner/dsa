/**
 * Implementation of smart pointers:
 * - atomic reference counting!
 * - function overload
 *
 * Reference:
 *
 * https://www.geeksforgeeks.org/how-to-implement-user-defined-shared-pointers-in-c/
 * https://en.cppreference.com/w/cpp/language/operator_incdec
 *
 */

#include <iostream>
#include <atomic>

using namespace std;

/**
 * Atomic counter for thread safety
 *
 */
class ICounter {
public:

    ICounter(const ICounter&) = delete;

    // deleted copy assignment
    ICounter& operator=(const ICounter&) = delete;

    // atomic increment/decrement operators
    int &operator++() { // without parameter indicates prefix operator!
        // pre-increment, ++a;
    }

    int operator++(int) {
        // post-increment, a++;
    }

    int operator--() {
        // pre-increment, a++;
    }
    int operator--(int) {
        // post-increment, a++;
    }
};

using Counter = std::atomic<int>;

template<class T>
class SharedPtr {
public:
    explicit SharedPtr(T *ptr = nullptr) {
        m_ptr = ptr;
        if (ptr) {
            m_counter = new Counter();
        }
    }

    // destructor: decrement reference counter
    // RAII
    ~SharedPtr() {
        if (m_counter && --(*m_counter) == 0) { // XXX: pre-decrement, thread safety
            delete m_counter;
            delete m_ptr;
        }
    }

    // copy constructor: increment reference counter
    SharedPtr(SharedPtr<T> &sp) {
        m_ptr = sp.m_ptr;
        m_counter = sp.m_counter;

        if (m_counter) (*m_counter)++;
    }

    // TODO: copy assignment

    // overload * operator to deference
    T& operator*() {
        return *m_ptr;
    }

    // overload -> operator
    T* operator->() {
        return m_ptr;
    }

	friend ostream& operator<<(ostream& os, SharedPtr<T> &sp) {
        cout << "Address pointed: " << sp.m_ptr << endl;
        cout << *(sp.m_counter) << endl;
        return os;
    }

private:
    // reference counter
    Counter *m_counter;
    T *m_ptr;
};

template<class T>
class UniquePtr {
private:
    T *m_ptr;
public:
    UniquePtr(T *ptr): m_ptr(ptr) { }
    UniquePtr(UniquePtr &obj) = delete; // copy constructor deleted
    UniquePtr& operator=(const UniquePtr<T> &obj) = delete; // copy assignment deleted

    T& operator*() { // * deference
        return *m_ptr;
    }

    T* operator->() {
        return this->m_ptr;
    }

    ~UniquePtr() { // desctructor
        if (m_ptr) delete m_ptr;
    }
};

int main()
{
    // ptr1 pointing to an integer.
    SharedPtr<int> ptr1(new int(151));
    cout << "--- Shared pointers ptr1 ---\n";
    *ptr1 = 100;
    cout << " ptr1's value now: " << *ptr1 << endl;
    cout << ptr1;

    {
        // ptr2 pointing to same integer
        // which ptr1 is pointing to
        // Shared pointer reference counter
        // should have increased now to 2.
        SharedPtr<int> ptr2 = ptr1;
        cout << "--- Shared pointers ptr1, ptr2 ---\n";
        cout << ptr1;
        cout << ptr2;

        {
            // ptr3 pointing to same integer
            // which ptr1 and ptr2 are pointing to.
            // Shared pointer reference counter
            // should have increased now to 3.
            SharedPtr<int> ptr3(ptr2);
            cout << "--- Shared pointers ptr1, ptr2, ptr3 "
                    "---\n";
            cout << ptr1;
            cout << ptr2;
            cout << ptr3;
        }

        // ptr3 is out of scope.
        // It would have been destructed.
        // So shared pointer reference counter
        // should have decreased now to 2.
        cout << "--- Shared pointers ptr1, ptr2 ---\n";
        cout << ptr1;
        cout << ptr2;
    }

    // ptr2 is out of scope.
    // It would have been destructed.
    // So shared pointer reference counter
    // should have decreased now to 1.
    cout << "--- Shared pointers ptr1 ---\n";
    cout << ptr1;

    return 0;
}
