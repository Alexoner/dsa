#include <iostream>
#include <memory>

/**
 * https://herbsutter.com/2008/01/01/gotw-88-a-candidate-for-the-most-important-const/
 *
 * a local const reference prolongs the lifetime of temporary values until the end of the containing scope, but saving you the cost of a copy-construction.
 */


using namespace std;

string f() { return "abc"; }

void g() {
  //string& s = f(); // compile error
  const string& s = f(); // const reference prolongs the lifetime of temporary value.
  cout << s << endl;    // can we still use the "temporary" object?
}

void freeConstPointer(std::shared_ptr< int const> p)
{
  //*p = 0;
  delete p.get(); // XXX: bypass const
}

void freeConstPointer(int * const p)
{
  //p = NULL; // compile error, pointer variable is const
  *p = 0;
  delete p;
}

void freeConstPointer(int const* p)
{
  //*p = 0;
  delete p;
}

int main(int argc, char *argv[])
{
    g();
    int *p = new int;
    freeConstPointer(p);
    std::shared_ptr<int> pi = make_shared<int>(0);
    freeConstPointer(pi);
    *pi = 1;

    return 0;
}
