#pragma once

#include <iostream>
#include <pthread.h>
#include <queue>
#include <vector>
#include <random>
#include <unistd.h>

using namespace std;

void* runLoop(void* data);
void *thr_func(void *data);


class ThreadPool {

private:
    // variables for thread safety
    pthread_mutex_t m_lock; // lock the task queue
    pthread_cond_t m_cond;  // tasks queue condition variabble
    // TODO: general meaningful task queue, not just such trivial one
    queue<int> m_tasks;

    vector<pthread_t> m_threads;
    pthread_attr_t m_thread_attr; // thread attributes

    bool should_shutdown; //
    bool dead;

public:
    ThreadPool(int size = 5)
    {
        should_shutdown = false;
        dead = false;

        // spawn threads
        pthread_mutex_init(&m_lock, NULL);
        pthread_cond_init(&m_cond, NULL);
        //m_cond = PTHREAD_COND_INITIALIZER;
        pthread_t tid;

        pthread_attr_init(&m_thread_attr);
        pthread_attr_setscope(&m_thread_attr, PTHREAD_SCOPE_SYSTEM);
        pthread_attr_setdetachstate(&m_thread_attr, PTHREAD_CREATE_DETACHED);
        int rc;
        cout << "creating " << size << " threads" << endl;
        for (int i = 0; i < size; i++) {
            if ((rc = pthread_create(&tid, NULL, runLoop, this))) {
                fprintf(stderr, "error: pthread_create, rc: %d\n", rc);
                exit(-1);
            }
            m_threads.push_back(tid);
        }
        cout << "initialized " << size << " threads" << endl;
    }

    ~ThreadPool() {
        if (!dead) {
            shutdown();
            // TODO: wait for join and destroy?
        }
    }

    void shutdown()
    {
        // shutdown with thread safety
        pthread_mutex_lock(&m_lock);
        should_shutdown = true;
        pthread_mutex_unlock(&m_lock);
        pthread_cond_broadcast(&m_cond);
        dead = true;
    }

#pragma mark - worker threads' functions

    void addTask(int task)
    {
        // synchronized task queue push operation
        pthread_mutex_lock(&m_lock);
        m_tasks.push(task);
        pthread_mutex_unlock(&m_lock);
        pthread_cond_signal(&m_cond);
    }

    int getTask()
    {
        // synchronized task queue pop operation
        pthread_mutex_lock(&m_lock);
        int task = NULL; // NULL for no task available: should shutdown
        while (m_tasks.empty() && !should_shutdown) {
            pthread_cond_wait(&m_cond, &m_lock);
        }
        if (!(m_tasks.empty())) {
            task = m_tasks.front();
            m_tasks.pop();
        }
        pthread_mutex_unlock(&m_lock);
        return task;
    }

    void workerLoop()
    {
        cout << "working" << endl;
        while (1) {
            if (should_shutdown) {
                // should shutdown: exit the run loop
                cout << "shutting down" << endl;
                break;
            }
            int task = getTask();
            if (!task) {
                // invalid task
                continue;
            }
            // TODO: actual job
            //cout << "Running task: " << task << endl;
            float r = (rand() % 10000) / 9999.0;
            sleep(r);
            printf( "Running task: %d after delay: %.2f\n", task, r);
        }
    }
};
