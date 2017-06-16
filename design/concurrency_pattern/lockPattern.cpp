#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

#define NUM_THREADS 5
#define MAX_COUNT 10

/* create thread argument struct for thr_func() */
typedef struct _thread_data_t {
  int tid;
  double stuff;
} thread_data_t;

/* shared data between threads */
double shared_x;
pthread_mutex_t lock_x;

/* thread function */
void *thr_func(void *arg) {
  thread_data_t *data = (thread_data_t *)arg;

  printf("hello from thr_func, thread id: %d\n", data->tid);
  /* get mutex before modifying and printing shared_x */
  pthread_mutex_lock(&lock_x);
    shared_x += data->stuff;
    printf("x = %f\n", shared_x);
  pthread_mutex_unlock(&lock_x);

  pthread_exit(NULL);
}

int count = 0;
pthread_mutex_t count_lock;
pthread_cond_t count_cond = PTHREAD_COND_INITIALIZER;

void *thr_func1(void *arg) {
  printf("waiting\n");
  /* thread code blocks here until MAX_COUNT is reached */
  pthread_mutex_lock(&count_lock);
    while (count < MAX_COUNT) {
      pthread_cond_wait(&count_cond, &count_lock);
    }
  fprintf(stdout, "condition count: done!\n");
  pthread_mutex_unlock(&count_lock);
  /* proceed with thread execution */

  pthread_exit(NULL);
}

/* some other thread code that signals a waiting thread that MAX_COUNT has been reached */
void *thr_func2(void *arg) {
  printf("mutating count\n");
  pthread_mutex_lock(&count_lock);

  /* some code here that does interesting stuff and modifies count */

  if (count == MAX_COUNT) {
    pthread_mutex_unlock(&count_lock);
    pthread_cond_signal(&count_cond);
  } else {
    count = MAX_COUNT;
    pthread_mutex_unlock(&count_lock);
  }

  pthread_exit(NULL);
}

int test_mutex() {
  pthread_t thr[NUM_THREADS];
  int i, rc;
  /* create a thread_data_t argument array */
  thread_data_t thr_data[NUM_THREADS];

  /* initialize shared data */
  shared_x = 0;

  /* initialize pthread mutex protecting "shared_x" */
  pthread_mutex_init(&lock_x, NULL);

  /* create threads */
  for (i = 0; i < NUM_THREADS; ++i) {
    thr_data[i].tid = i;
    thr_data[i].stuff = (i + 1) * NUM_THREADS;
    if ((rc = pthread_create(&thr[i], NULL, thr_func, &thr_data[i]))) {
      fprintf(stderr, "error: pthread_create, rc: %d\n", rc);
      return EXIT_FAILURE;
    }
  }
  /* block until all threads complete */
  for (i = 0; i < NUM_THREADS; ++i) {
    pthread_join(thr[i], NULL);
  }

  return EXIT_SUCCESS;
}

int test_condition() {

  int n = 2;
  pthread_t thr[n];
  int i, rc;
  /* create a thread_data_t argument array */
  thread_data_t thr_data[n];

  /* initialize shared data */
  count = 0;

  /* initialize pthread mutex protecting "shared_x" */
  pthread_mutex_init(&lock_x, NULL);

  /* create threads */
  for (i = 0; i < n; ++i) {
    thr_data[i].tid = i;
    if ((rc = pthread_create(&thr[i], NULL, !i ? thr_func1: thr_func2, &thr_data[i]))) {
      fprintf(stderr, "error: pthread_create, rc: %d\n", rc);
      return EXIT_FAILURE;
    }
  }
  /* block until all threads complete */
  for (i = 0; i < NUM_THREADS; ++i) {
    pthread_join(thr[i], NULL);
  }
  return EXIT_SUCCESS;
}

int main(int argc, char **argv) {
  test_mutex();

  test_condition();

  return EXIT_SUCCESS;
}
