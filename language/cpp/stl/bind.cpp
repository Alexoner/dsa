// bind example
#include <iostream>     // std::cout
#include <functional>   // std::bind
#include <debug.hpp>

// a function: (also works with function object: std::divides<double> my_divide;)
double my_divide (double x, double y) {
  double z =  x/y;
  std::cout << z << std::endl;
  return z;
}

struct MyPair {
  double a,b;
  double multiply() {
      double z =  a*b;
      std::cout << z << std::endl;
      return z;
  }
};

void callback(int ret, vector<int> &&results)
{
  cout << "return code: " << ret << ", result: " << results;
}

int main () {
  using namespace std::placeholders;    // adds visibility of _1, _2, _3,...

  // binding functions:
  auto fn_five = std::bind (my_divide,10,2);               // returns 10/2
  assert(fn_five() == 5);                          // 5

  function<double(double)> fn_half = std::bind (my_divide,_1,2);               // returns x/2
  assert(fn_half(10) == 5);                        // 5

  function<double(double, double)> fn_invert = std::bind (my_divide,_2,_1);            // returns y/x
  assert(fn_invert(10, 2) == 0.2);                    // 0.2

  function<double(double, double)> fn_rounding = std::bind<int> (my_divide,_1,_2);     // returns int(x/y)
  assert(fn_rounding(10, 3) == 3);                  // 3

  MyPair ten_two {10,2};

  // binding members:
  auto bound_member_fn = std::bind (&MyPair::multiply,_1); // returns x.multiply()
  assert(bound_member_fn(ten_two) == 20);           // 20

  auto bound_member_data = std::bind (&MyPair::a,ten_two); // returns ten_two.a
  assert(bound_member_data() == 10);                // 10

  auto cb = bind(&callback, 0, _1);
  cb(vector<int>{1, 2, 3, 4});

  return 0;
}
