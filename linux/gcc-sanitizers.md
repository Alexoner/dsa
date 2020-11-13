### [Sanitizers](https://github.com/google/sanitizers)

- ASan: Address Sanitizer detects use-after-free, buffer-overflow, and leaks.
- TSAN: Thread Sanitizer detects data races, deadlocks.
- MSAN: Memory Sanitizer detects uses of uninitialized memory.
- UBSan: Undefined Behavior Sanitizer detects… that

New tools, based on compiler instrumentation, ~2x slow down(https://www.usenix.org/sites/default/files/conference/protected-files/enigma_slides_serebryany.pdf).
Available in LLVM and GCC(with higher version>=6).

```cpp
/*
 * a.cpp
 */
#include <stdlib.h>

void *p;

int main() {
  p = malloc(7);
  p = 0; // The memory is leaked here.
  return 0;
}
```

Compile the source code with compiler's [sanitizer flags](https://github.com/google/sanitizers/wiki/AddressSanitizerFlags):

    g++ -std=c++11 -g -fsanitize=address a.cpp

Run the binary with appropriate `ASAN_OPTION`: 

    export ASAN_OPTIONS=detect_leaks=1:abort_on_error=1:disable_coredump=0:unmap_shadow_on_exit=1
    ./a.out
    =================================================================
    ==32182==ERROR: LeakSanitizer: detected memory leaks

    Direct leak of 7 byte(s) in 1 object(s) allocated from:
        #0 0x4b8af8  (/tmp/build/a.out+0x4b8af8)
        #1 0x4ece5a  (/tmp/build/a.out+0x4ece5a)
        #2 0x7f5bda8e182f  (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

    SUMMARY: AddressSanitizer: 7 byte(s) leaked in 1 allocation(s).

Use-after-free:

    /**
     * a.cpp
     */
    int main(int argc, char **argv) {
      int *array = new int[100];
      delete [] array;
      return array[argc]; 
    }

Compile with address sanitizer and run:

    clang++ -O0 -std=c++11 -fsanitize=address a.cpp && ./a.out
    =================================================================
    ==2565==ERROR: AddressSanitizer: heap-use-after-free on address 0x61400000fe44 at pc 0x0000004eced2 bp 0x7ffc4c3f7440 sp 0x7ffc4c3f7438
    READ of size 4 at 0x61400000fe44 thread T0
    #0 0x4eced1  (/tmp/build/a.out+0x4eced1)
    #1 0x7f0b31cfa82f  (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)
    #2 0x4189e8  (/tmp/build/a.out+0x4189e8)

    0x61400000fe44 is located 4 bytes inside of 400-byte region [0x61400000fe40,0x61400000ffd0)
    freed by thread T0 here:
    #0 0x4ea840  (/tmp/build/a.out+0x4ea840)
    #1 0x4ece86  (/tmp/build/a.out+0x4ece86)
    #2 0x7f0b31cfa82f  (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

    previously allocated by thread T0 here:
    #0 0x4ea240  (/tmp/build/a.out+0x4ea240)
    #1 0x4ece64  (/tmp/build/a.out+0x4ece64)
    #2 0x7f0b31cfa82f  (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)

    SUMMARY: AddressSanitizer: heap-use-after-free (/tmp/build/a.out+0x4eced1)
    Shadow bytes around the buggy address:
    ...


#### How to check memory of a running process - Use gdb to call check function?

To use address sanitizer or leak sanitizer under `ptrace`(gdb, strace), we need to set:

    export LSAN_OPTIONS=detect_leaks=0

Then use gdb:

    gdb -p pid
    (gdb) break __sanitizer::Die
    (gdb) c
    (gdb) call __lsan_do_leak_check () # tips: tab can complete


The problem is, where did the output go?


#### Control flow sanitizer

    // a.c

    void Bad() { puts("BOOO"); }
    struct Expr {
     long a[2];
     long (*Op)(long *);
    };
    int main(int argc, char **argv) {
     struct Expr e;
     e.a[2 * argc] = (long)&Bad;
     e.Op(e.a);
    }

Compile and run:

    $ clang a.c && ./a.out
    BOOO
    $ clang -flto -fsanitize=cfi -fvisibility=hidden a.c && ./a.out
    Illegal instruction (core dumped)

#### Stack buffer overflow 

    // a.cpp
    void Bad() { puts("BOOO"); exit(0); }
    int main(int argc, char **argv) {
     long array[10];
     array[argc * 13] = (long)&Bad;
    }

Compile and run:

    % clang a.c && ./a.out
    BOOO
    % clang -fsanitize=safe-stack a.c && ./a.out
    [1]    10408 segmentation fault (core dumped)  ./a.out

### Set thread name

```cpp
    pthread_setname_np(pthread_self(), "thread_name");
```


