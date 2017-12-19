# C++ Concurrency in Action notes, common pitfalls

## Managing threads
- Avoid dangling reference or pointers(passed to another thread)

## Sharing data between threads

### RACE CONDITION
- Don't pass pointers and references to protected data outside the scope of the lock, whether by returning them from a function, storing them in externally visible memory, or passing them as arguments to user-supplied functions

### DEADLOCK
Guideline idea to avoid deadlock: don't wait for another thread if there's a chance it's waiting for you.

- Avoid nested locks(ALL-OR-NOTHING, like atomic idea). std::lock provides all-or-nothing semantics with regard to locking supplied mutexes.
- Acquire locks in a FIXED ORDER.
- Avoid calling a user-supplied code while holding a lock
- Use a lock HIERARCHY.
