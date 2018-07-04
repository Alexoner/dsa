/**
 *
 * Source: cppreference (http://en.cppreference.com/w/cpp/algorithm/accumulate)
 *
 */

#include "easylogging++.h"
INITIALIZE_EASYLOGGINGPP

#include <assert.h>

#include <debug.hpp>

#include <iostream>
#include <vector>
#include <numeric>
#include <string>
#include <functional>

using namespace std;


int main()
{
    std::vector<int> v{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

    LOG(DEBUG) << "vector of int: " << v << endl;

    // compute sum
    int sum = std::accumulate(v.begin(), v.end(), 0);

    // compute product
    int product = std::accumulate(v.begin(), v.end(), 1, std::multiplies<int>());

    // string
    std::string s = std::accumulate(std::next(v.begin()), v.end(),
                                    std::to_string(v[0]), // start with first element
                                    [](std::string a, int b) {
                                        return a + '-' + std::to_string(b);
                                    });

    // string join
    std::string joinedString = std::accumulate(v.begin(), v.end(),
            std::string(""),
            [](std::string a, int b) {
                return a + std::to_string(b);
            }
            );

    std::vector<string> splitString;
    std::accumulate(joinedString.begin(), joinedString.end(),
                0,
                [&](char a, char b) {
                    splitString.push_back(to_string(b));
                    return 0;
                    //return a;
                }
            );

    LOG(DEBUG) << "splitString: " << splitString << endl;

    std::string vectorAsString = std::accumulate(
            v.begin(),
            v.end(),
            string("{"),
            [](string a, char b) {
                return a + std::to_string(b) + ", ";
            }
            ) + string("}");

    assert(vectorAsString == to_string(v));

    LOG(DEBUG) << "sum: " << sum;
    LOG(DEBUG) << "product: " << product;
    LOG(DEBUG) << "dash-separated string: " << s;
    LOG(DEBUG) << "joined string: " << joinedString;
    LOG(DEBUG) << "vector as string: " << vectorAsString;
    LOG(DEBUG) << "vector as string: " << vectorAsString;
}
