#include <memory>
#include <iostream>
#include <cassert>

using namespace std;

int gi1 = 0;
int gi2;

string gs1 = "hello";
string gs2;

class Printer {
public:
    Printer(string a): sref(a){};

    string &sref;
};

int testStack() {
    cout << "testing stack" << endl;

    // test stack variable scope;
    int *pn = NULL;
    {
        int n;
        pn = &n;
        cout << "stack address: " << &n << ", value: " << n << endl;
    }

    {
        int n;
        cout << "stack address: " << &n << ", value: " << n << endl;
        assert(pn == &n); // XXX: will fire if using address sanitizer
    }

    std::shared_ptr<Printer> pPrinter;



    return 0;
}

int main(int argc, char **argv) {
    testStack();
    return 0;
}
