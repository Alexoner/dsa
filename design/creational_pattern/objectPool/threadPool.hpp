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
    vector<pthread_t> m_threads;
    // TODO: general meaningful task queue, not just such trivial one
    queue<int> m_tasks;
    pthread_mutex_t m_tasks_lock; // lock the task queue
    pthread_cond_t m_tasks_cond;  // tasks queue condition variabble

public:
    ThreadPool(int size = 5)
    {
    //m_threads = vector<pthread_t>(size);
    pthread_mutex_init(&m_tasks_lock, NULL);
    pthread_cond_init(&m_tasks_cond, NULL);
    //m_tasks_cond = PTHREAD_COND_INITIALIZER;
    pthread_t tid;
    int rc;
    cout << "creating " << size << " threads" << endl;
    for (int i = 0; i < size; i++) {
        //pthread_create(&tid, NULL, runLoop, this);
    if ((rc = pthread_create(&tid, NULL, runLoop, this))) {
      fprintf(stderr, "error: pthread_create, rc: %d\n", rc);
      exit(-1);
    }
        m_threads.push_back(tid);
    }
    cout << "initialized " << size << " threads" << endl;
    }

    void addTask(int task)
    {
        pthread_mutex_lock(&m_tasks_lock);
        m_tasks.push(task);
        pthread_mutex_unlock(&m_tasks_lock);
        pthread_cond_signal(&m_tasks_cond);
    }

    int getTask()
    {
    pthread_mutex_lock(&m_tasks_lock);
    while (m_tasks.empty()) {
        pthread_cond_wait(&m_tasks_cond, &m_tasks_lock);
    }
    int task = m_tasks.front();
    m_tasks.pop();
    pthread_mutex_unlock(&m_tasks_lock);
    return task;
    }

    void workerLoop()
    {
        cout << "working" << endl;
    while (1) {
        int task = getTask();
        // TODO: actual job
        //cout << "Running task: " << task << endl;
        int r = rand() % 2;
        sleep(r);
        printf( "Running task: %d after delay: %d\n", task, r);
    }
    }
};
