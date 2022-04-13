/**
 * benchmark test context switch latency
 * https://stackoverflow.com/questions/304752/how-to-estimate-the-thread-context-switching-overhead
 *
 */
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <pthread.h>
#include <sys/time.h>
#include <unistd.h>

uint32_t COUNTER;
pthread_mutex_t LOCK;
pthread_mutex_t START;
pthread_cond_t CONDITION;

void * threads (
    void * unused
) {
    // Wait till we may fire away
    pthread_mutex_lock(&START);
    pthread_mutex_unlock(&START);

    pthread_mutex_lock(&LOCK);
    // If I'm not the first thread, the other thread is already waiting on
    // the condition, thus Ihave to wake it up first, otherwise we'll deadlock
    if (COUNTER > 0) {
        pthread_cond_signal(&CONDITION);
    }
    for (;;) {
        COUNTER++;
        pthread_cond_wait(&CONDITION, &LOCK);
        // Always wake up the other thread before processing. The other
        // thread will not be able to do anything as long as I don't go
        // back to sleep first.
        pthread_cond_signal(&CONDITION);
    }
    pthread_mutex_unlock(&LOCK); //To unlock
}

int64_t timeInMS ()
{
    struct timeval t;

    gettimeofday(&t, NULL);
    return (
        (int64_t)t.tv_sec * 1000 +
        (int64_t)t.tv_usec / 1000
    );
}


int main (
    int argc,
    char ** argv
) {
    int64_t start;
    pthread_t t1;
    pthread_t t2;
    int64_t myTime;

    pthread_mutex_init(&LOCK, NULL);
    pthread_mutex_init(&START, NULL);
    pthread_cond_init(&CONDITION, NULL);

    pthread_mutex_lock(&START);
    COUNTER = 0;
    pthread_create(&t1, NULL, threads, NULL);
    pthread_create(&t2, NULL, threads, NULL);
    pthread_detach(t1);
    pthread_detach(t2);
    // Get start time and fire away
    myTime = timeInMS();
    pthread_mutex_unlock(&START);
    // Wait for about a second
    sleep(1);
    // Stop both threads
    pthread_mutex_lock(&LOCK);
    // Find out how much time has really passed. sleep won't guarantee me that
    // I sleep exactly one second, I might sleep longer since even after being
    // woken up, it can take some time before I gain back CPU time. Further
    // some more time might have passed before I obtained the lock!
    myTime = timeInMS() - myTime;
    // Correct the number of thread switches accordingly
    COUNTER = (uint32_t)(((uint64_t)COUNTER * 1000) / myTime);
    printf("Number of thread switches in about one second was %u\n", COUNTER);
    return 0;
}
