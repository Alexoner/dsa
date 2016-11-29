#ifndef DEFINE_H
#define DEFINE_H
//this is for binsearch
extern int binsearch(int *a,int n,int key);
//end of binsearch

//this is for linkedlist
typedef struct node
{
    int data;
    struct node *prev,*next;
}Lnode,*Llist;

extern void init(Llist *L);
extern void insert(Llist *L,Llist q,int item);
extern void show(Llist end);
extern void destroy(Llist *L);
//end of linkedlist

//for quicksort
extern void quicksort(int *a,int p,int r);

//for swap
extern void swap(int *x,int *y);
//end of swap

//for heapsort
int heap_size;
extern void max_heapify(int *a,int i);
//extern void heapsort(int *a);
extern void build_max_heap(int *a);
//end of heapsort

#endif

