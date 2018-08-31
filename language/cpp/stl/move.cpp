#include <debug.hpp>


int main()
{
    std::string str = "Hello";
    std::vector<std::string> v;

    cout << "str is \"" << str << "\"\n";
    // uses the push_back(const T&) overload, which means
    // we'll incur the cost of copying str
    v.push_back(str);
    std::cout << "After copy, str is \"" << str << "\"\n";

    std::move(str); //
    std::cout << "After move without assignment, str is \"" << str << "\"\n";

    // uses the rvalue reference push_back(T&&) overload,
    // which means no strings will be copied; instead, the contents
    // of str will be moved into the vector.  This is less
    // expensive, but also means str might now be empty.
    v.push_back(std::move(str));
    std::cout << "After move, str is \"" << str << "\"\n";

    std::cout << "The contents of the vector are \"" << v[0]
                                         << "\", \"" << v[1] << "\"\n";

    vector<string> v1;
    v1 = std::move(v);

    std::cout << "After move v1 = move(v), vector v is \"" << v << "\"\n";
    std::cout << "After move v1 = move(v), vector v1 is \"" << v1 << "\"\n";

    std::cout << "Moving each element" << endl;
    for (string &x: v1) {
        string y = std::move(x);
    }
    std::cout << "After moving each element, v1: " << v1 << endl;

    int i = int(1 << 16);
    int j = std::move(i);
    std::cout << "After move j = move(i), i = " << i << ", j = " << j << endl;

}
