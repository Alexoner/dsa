#include <debug.hpp>

int main(int argc, char *argv[])
{
    vector<int> a {1, 2, 3};
    vector<int> b {1, 2, 3};
    cout << "a: " << a << endl;
    cout << "b: " << b << endl;
    transform(a.begin(), a.end(),
            b.begin(), a.begin(),
            std::plus<int>());
    cout << "a + b" << a << endl;
    a = {1, 2, 3};
    transform(a.begin(), a.end(),
            b.begin(), a.begin(),
            [](int x, int y) -> int {
                return x + 2 * y;
            });
    cout << "a + 2 * b" << a << endl;
    return 0;
}
