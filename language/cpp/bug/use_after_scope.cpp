// RUN: clang -O -g -fsanitize=address -fsanitize-address-use-after-scope \
//    use-after-scope.cpp -o /tmp/use-after-scope
// RUN: /tmp/use-after-scope

// Check can be disabled in run-time:
// RUN: ASAN_OPTIONS=detect_stack_use_after_scope=0 /tmp/use-after-scope

volatile int *p = 0;

int main() {
  {
    int x = 0;
    p = &x;
  }
  *p = 5;
  return 0;
}

/**
 * Expect:
=================================================================
==12630==ERROR: AddressSanitizer: stack-use-after-scope on address 0x7ffef5d81bb0 at pc 0x000000400999 bp 0x7ffef5d81b80 sp 0x7ffef5d81b78
WRITE of size 4 at 0x7ffef5d81bb0 thread T0
    #0 0x400998 in main /home/hao.du/Documents/mine/dsa/language/cpp/bug/use_after_scope.cpp:15
    #1 0x7fb7b3fbb82f in __libc_start_main (/lib/x86_64-linux-gnu/libc.so.6+0x2082f)
    #2 0x4007e8 in _start (/home/hao.du/Documents/mine/dsa/language/cpp/bug/a.out+0x4007e8)

Address 0x7ffef5d81bb0 is located in stack of thread T0 at offset 32 in frame
    #0 0x4008a1 in main /home/hao.du/Documents/mine/dsa/language/cpp/bug/use_after_scope.cpp:10

  This frame has 1 object(s):
    [32, 36) 'x' <== Memory access at offset 32 is inside this variable
HINT: this may be a false positive if your program uses some custom stack unwind mechanism or swapcontext
      (longjmp and C++ exceptions *are* supported)
SUMMARY: AddressSanitizer: stack-use-after-scope /home/hao.du/Documents/mine/dsa/language/cpp/bug/use_after_scope.cpp:15 in main
Shadow bytes around the buggy address:
  0x10005eba8320: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x10005eba8330: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x10005eba8340: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x10005eba8350: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x10005eba8360: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
=>0x10005eba8370: 00 00 f1 f1 f1 f1[f8]f2 f2 f2 f3 f3 f3 f3 00 00
  0x10005eba8380: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x10005eba8390: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x10005eba83a0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x10005eba83b0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  0x10005eba83c0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
Shadow byte legend (one shadow byte represents 8 application bytes):
  Addressable:           00
  Partially addressable: 01 02 03 04 05 06 07
  Heap left redzone:       fa
  Freed heap region:       fd
  Stack left redzone:      f1
  Stack mid redzone:       f2
  Stack right redzone:     f3
  Stack after return:      f5
  Stack use after scope:   f8
  Global redzone:          f9
  Global init order:       f6
  Poisoned by user:        f7
  Container overflow:      fc
  Array cookie:            ac
  Intra object redzone:    bb
  ASan internal:           fe
  Left alloca redzone:     ca
  Right alloca redzone:    cb
==12630==ABORTING
 *
 */
