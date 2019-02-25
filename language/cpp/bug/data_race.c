/**
 * $ clang -fsanitize=thread -g -O1 tiny_race.c
 * $ ./a.out
 * expecting:
==================
WARNING: ThreadSanitizer: data race (pid=2195)
  Write of size 4 at 0x00000060107c by thread T1:
    #0 Thread1 /home/hao.du/Documents/mine/dsa/language/cpp/bug/tiny_race.c:29 (tiny_race+0x000000400aad)
    #1 <null> <null> (libtsan.so.0+0x0000000230d9)

  Previous write of size 4 at 0x00000060107c by main thread:
    #0 main /home/hao.du/Documents/mine/dsa/language/cpp/bug/tiny_race.c:36 (tiny_race+0x000000400b01)

  Location is global 'Global' of size 4 at 0x00000060107c (tiny_race+0x00000060107c)

  Thread T1 (tid=2197, running) created by main thread at:
    #0 pthread_create <null> (libtsan.so.0+0x000000027577)
    #1 main /home/hao.du/Documents/mine/dsa/language/cpp/bug/tiny_race.c:34 (tiny_race+0x000000400af7)

SUMMARY: ThreadSanitizer: data race /home/hao.du/Documents/mine/dsa/language/cpp/bug/tiny_race.c:29 Thread1
==================
ThreadSanitizer: reported 1 warnings
 *
 */
#include <pthread.h>

int Global;
void *Thread1(void *x) {
  Global = 42;
  return x;
}
int main() {
  pthread_t t;
  pthread_create(&t, NULL, Thread1, NULL);

  Global = 43;
  pthread_join(t, NULL);
  return Global;
}
