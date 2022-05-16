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

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>

int64_t timeInMS ()
{
    struct timeval t;

    gettimeofday(&t, NULL);
    return (
        (int64_t)t.tv_sec * 1000 +
        (int64_t)t.tv_usec / 1000
    );
}

uint32_t COUNTER = 0;
uint32_t COUNTER_MEMORY = 0;

void *thread_file(void *data) {
    while (true) {
        COUNTER++;
        int fd = open("/tmp/test", O_RDONLY|O_CREAT);
        close(fd);
    }
}

void *thread_memory(void *data) {
    while (true) {
        COUNTER_MEMORY++;
        int size = 1024; // 4kB
        // size = 8;
        int arr[size];
        memset(arr, 0, size*sizeof(int));
    }
}

int main (
    int argc,
    char ** argv
) {
    int64_t start;
    pthread_t t1;
    pthread_t t2;
    int64_t myTime;

    pthread_create(&t1, NULL, thread_file, NULL);
    pthread_detach(t1);
    pthread_create(&t2, NULL, thread_memory, NULL);
    pthread_detach(t2);

    // Get start time and fire away
    myTime = timeInMS();
    // Wait for about a second
    sleep(1);
    // Stop both threads

    // Find out how much time has really passed. sleep won't guarantee me that
    // I sleep exactly one second, I might sleep longer since even after being
    // woken up, it can take some time before I gain back CPU time. Further
    // some more time might have passed before I obtained the lock!
    myTime = timeInMS() - myTime;
    // Correct the number of thread switches accordingly
    COUNTER = (uint32_t)(((uint64_t)COUNTER * 1000) / myTime);
    printf("Number of file open & close in about one second was %u\n", COUNTER);
    printf("File throughput: %u\n", COUNTER);
    printf("File latency: %.3e\n", 1.0f/COUNTER);

    printf("Number of 4KB memory access in about one second was %u\n", COUNTER_MEMORY);
    printf("Memory throughput: %u. (Not bandwidth!).\n", COUNTER_MEMORY);
    printf("Memory latency: %.3e\n", 1.0f/COUNTER_MEMORY);

    return 0;
}

