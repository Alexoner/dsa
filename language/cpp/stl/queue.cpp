#include <debug.hpp>

// priority_queue::emplace
#include <iostream>       // std::cout
#include <queue>          // std::priority_queue
#include <string>         // std::string

int main ()
{
  std::priority_queue<std::string, vector<string>, std::greater<string>> mypq;

  mypq.emplace("orange");
  mypq.emplace("strawberry");
  mypq.emplace("apple");
  mypq.emplace("pear");

  mypq.push("hello");
  mypq.push("world");

  std::cout << "mypq contains:";
  while (!mypq.empty())
  {
     std::cout << ' ' << mypq.top();
     mypq.pop();
  }
  std::cout << '\n';

  return 0;
}
