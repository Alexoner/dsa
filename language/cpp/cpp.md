# Features of C++
- REFERENCE variables and POINTER variables
- Deterministic destruction of object
- Inheritance: virtual function
- Template
- Data structures and algorithms: STL
- Concurrency: threads, lock, lock free, wait free.

# Memory Management

## [RAII(Resource Acquisition is Initialization)](http://en.wikipedia.org/wiki/RAII)
Resource is hold only in the life cycle.

### [Smart Pointers](https://en.wikipedia.org/wiki/Smart_pointer)
Smart pointers are RAII classes implemented with REFERENCE COUNTING.
Most of crash bugs are caused by referencing a destructed object.
1. Parent-child relation: avoid CIRCULAR REFERENCES of shared_ptr!
2. Pass smart pointers instead of raw pointers
3. For asynchronous/multi-threaded programs, pass smart pointers consistently.

Reference:
[shared_ptr](http://en.cppreference.com/w/cpp/memory/shared_ptr)
[weak_ptr](http://en.cppreference.com/w/cpp/memory/weak_ptr)

# Architecture

## Architecture as a collection of Data Structures

## Use STATE MACHINE, instead of nested callback functions!
Callback hell is evil!

## Parse STATE/DATA, instead of using callback functions

## Synchronize data between threads using lock, signal, variables

## Encapsulate low-level resources as classes, and wrap objects with smart pointers to manage the resource releasing automatically

## Implement getter and setter methods, if properties are from member objects, not member variables
1. Subclasses inheriting the base class can capture the member property change event
2. The member property is dynamic

## Thread safety, thread synchronization
1. State with lock 
2. Use RAII. In multi-threaded scenario, an asynchronous thread referencing an object that may be destroyed by another thread.
Solution:
- Use shared_ptr as strong reference to that object in the asynchronous thread, and the destroying thread never manually release resources, just decrease its reference.
- Use weak_ptr to check whether it has expired. Still, the resource should not be destroyed manually, instead, be managed with its life span.


# [Design Patterns](https://en.wikipedia.org/wiki/Software_design_pattern)
- Creational patterns
	- Singleton: Ensure a class has only one instance, and provide a global point of access to it.
	- Resource acquisition is initialization (RAII): Ensure that resources are properly released by tying them to the lifespan of suitable objects
	- Object pool: Avoid expensive acquisition and release of resources by recycling objects that are no longer in use. Can be considered a generalisation of connection pool and thread pool patterns.
	- Abstract factory: Provide an interface for creating families of related or dependent objects without specifying their concrete classes.
- Structural patterns
	- Decorator: Attach additional responsibilities to an object dynamically keeping the same interface. Decorators provide a flexible alternative to subclassing for extending functionality.
- Behavioural patterns
	- State: Allow an object to alter its behavior when its internal state changes. The object will appear to change its class.
	- Iterator: Provide a way to access the elements of an aggregate object sequentially without exposing its underlying representation.
	- Observer: Define a one-to-many dependency between objects where a state change in one object results in all its dependents being notified and updated automatically.
	- Null object: Avoid null references by providing a default object.
- Concurrency patterns
	- Lock: One thread puts a "lock" on a resource, preventing other threads from accessing or modifying it.
	- Thread pool: A number of threads are created to perform a number of tasks, which are usually organized in a queue. Typically, there are many more tasks than threads. Can be considered a special case of the object pool pattern.
	- Thread-specific storage: Static or "global" memory local to a thread.
	- Monitor object: An object whose methods are subject to mutual exclusion, thus preventing multiple objects from erroneously trying to use it at the same time.



# Common bugs
1. Most of crashes are due to wrong/NULL pointers
2. NULL pointers appear when not initialized, sub-routines return NULL, objects destructed early!
3. Jittering problem
Memory unstable: occupied with other data! This is likely due to objects are
destructed early, watch the life cycle of objects!
4. For NUMERICAL computation programs, pay attention to MEMORY allocation and input DATA FORMAT!
5. Use make_shared when constructing objects for shared_ptr to improve performance by using a single dynamic memory allocation.

```c++
// weak_ptr::expired example
#include <iostream>
#include <memory>

int main () {
  std::shared_ptr<int> shared (new int(10));
  std::weak_ptr<int> weak(shared);

  std::cout << "1. weak " << (weak.expired()?"is":"is not") << " expired\n";

  shared.reset();

  std::cout << "2. weak " << (weak.expired()?"is":"is not") << " expired\n";

  return 0;
}
```

### Coding tricks

#### STL containers will take care of elements' release automatically, but not allocated memory

#### Macros

```cpp
#define DEBUG_NEW new(__FILE__, __LINE__)
#define new DEBUG_NEW

```

### Performance

#### Notation & Terminology
- QPS: query per second
- TPS (transactions per second): the number of transactions executed per second. In other words, it can be calculated based on how many transactions are executed over a certain duration of the test and then calculate it for a second. It's a rate of transactions w.r.t. time, it is also called as throughput
- RT: response time

#### TPS, concurrency, RT
There are two types of bound: I/O bound, CPU bound.

I/O bound:
```
TPS = (memory / worker memory)  * (1 / Task time)
```

CPU bound:
```
TPS = Num. cores * (1 /Task time)
```
,which is similar to Little's Law:
$$
Average number of users in the system = average response time * throughput
N  =  T  *  X
$$

where, $N = Number of users, T = RT (average response time), X = TPS$

