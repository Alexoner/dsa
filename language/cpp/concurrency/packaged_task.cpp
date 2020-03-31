#include <cmath>
#include <chrono>
#include <cstdlib>
#include <vector>
#include <chrono>
#include <iostream>
#include <future>
#include <thread>

int main(void)
{
  const long N = 100*1000*1000;
  std::vector<double> array(N);
  for (auto& i : array)
    i = rand()/333.;

  std::cout << "timing raw" << std::endl;
  std::chrono::time_point<std::chrono::system_clock> start, end;
  start = std::chrono::system_clock::now();
  for (auto& i : array)
    pow(i,i);
  end = std::chrono::system_clock::now();
  std::chrono::duration<double> elapsed_seconds = end-start;
  std::cout << "elapsed time: " << elapsed_seconds.count() << "s\n\n";

  std::cout << "timing ptask" << std::endl;
  start = std::chrono::system_clock::now();
  std::packaged_task<double(double,double)> myTask(pow);
  for (auto& i : array)
  {
      myTask(i, i);
      myTask.get_future().wait();
      myTask.reset();
  }
  elapsed_seconds = std::chrono::system_clock::now()-start;
  std::cout << "elapsed time: " << elapsed_seconds.count() << "s\n\n";
  return 0;
}
