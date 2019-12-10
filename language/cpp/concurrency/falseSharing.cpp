#include <sys/times.h>
#include <time.h>
#include <stdio.h>
#include <pthread.h>



struct timespec tpBegin1,tpEnd1,tpBegin2,tpEnd2,tpBegin3,tpEnd3;  //These are inbuilt structures to store the time point related activities

double compute(struct timespec start,struct timespec end) //computes time in milliseconds given endTime and startTime timespec structures.
{
  double t;
  t=(end.tv_sec-start.tv_sec)*1000;
  t+=(end.tv_nsec-start.tv_nsec)*0.000001;

  return t;
}

int array[100];
int gTestCount = 100000000;

void *readValue(void *param)
{
  int   index = *((int*)param);
  int result = 0;
  for (int i = 0; i < gTestCount; i++)
  {
    result += array[index];
  }

}

void *writeValue(void *param) {
  int   index = *((int*)param);
  int   i;
  for (i = 0; i < gTestCount; i++)
    array[index]+=1;
}

int main(int argc, char *argv[]) {
  int       first_elem  = 0;
  int       bad_elem    = 1; // data sharing same cache line with first element
  int       good_elem   = 64; // data using different cache line with first element

  double time1;
  double time2;
  double time3;

  //---------------------------START--------Serial Computation---------------------------------------------

  {
    clock_gettime(CLOCK_REALTIME,&tpBegin1);
    writeValue((void*)&first_elem);
    //writeValue((void*)&bad_elem);
    readValue((void*)&bad_elem);
    clock_gettime(CLOCK_REALTIME,&tpEnd1);
  }

  //---------------------------END----------Serial Computation---------------------------------------------

  pthread_t     thread_1;
  pthread_t     thread_2;
  //---------------------------START--------parallel computation with False Sharing----------------------------
  {
    clock_gettime(CLOCK_REALTIME,&tpBegin2);
    pthread_create(&thread_1, NULL,writeValue, (void*)&first_elem);
    //pthread_create(&thread_2, NULL,writeValue, (void*)&bad_elem);
    pthread_create(&thread_2, NULL,readValue, (void*)&bad_elem);
    pthread_join(thread_1, NULL);
    pthread_join(thread_2, NULL);
    clock_gettime(CLOCK_REALTIME,&tpEnd2);
  }

  //---------------------------END----------parallel computation with False Sharing-------------


  //---------------------------START--------parallel computation without False Sharing----------

  {
    clock_gettime(CLOCK_REALTIME,&tpBegin3);
    pthread_create(&thread_1, NULL,writeValue, (void*)&first_elem);
    //pthread_create(&thread_2, NULL,writeValue, (void*)&good_elem);
    pthread_create(&thread_2, NULL,readValue, (void*)&good_elem);
    pthread_join(thread_1, NULL);
    pthread_join(thread_2, NULL);
    clock_gettime(CLOCK_REALTIME,&tpEnd3);
  }

  //---------------------------END--------parallel computation without False Sharing------------


  //--------------------------START------------------OUTPUT STATS-------------------------------
  printf("array[first_element]: %d\t\t array[bad_element]: %d\t\t array[good_element]: %d\n\n\n", array[first_elem],array[bad_elem],array[good_elem]);


  time1 = compute(tpBegin1,tpEnd1);
  time2 = compute(tpBegin2,tpEnd2);
  time3 = compute(tpBegin3,tpEnd3);
  printf("Time taken in Sequential computing : %f ms\n", time1);
  printf("Time take with false sharing      : %f ms\n", time2);
  printf("Time taken without false sharing  : %f ms\n", time3);

  //--------------------------END------------------OUTPUT STATS---------------------------------


  return 0;
}
