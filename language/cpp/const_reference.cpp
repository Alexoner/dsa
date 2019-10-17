#include <iostream>

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

int main(int argc, char *argv[])
{
    g();
    return 0;
}
