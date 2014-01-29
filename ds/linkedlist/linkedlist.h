#ifndef DLINKEDLIST_H
#define DLINKEDLIST_H

#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

#undef offsetof
#define offsetof(TYPE, MEMBER) ((size_t) &((TYPE *)0)->MEMBER)

typedef struct list List;
//typedef struct list;

//struct list
//{
//int datasize;
//int length;
////int empty;
//struct list *head;
//struct list *tail;
//pthread_mutex_t lock; //mutex lock for thread safe
//};

struct list
{
    void *data;
    struct list  *prev;
    struct list *next;
};

struct list *node_new(void *data);
struct list *node_new_int(int i);
struct list *node_new_num(double f);

int compare_int(void *x, void *y);
float compare_float(void *x, void *y);
double comare_double(void *x, void *y);

struct list *node_destroy(struct list *p, void* data_destroy(void*));

struct list *list_init(struct list *list);

struct list *list_destroy(struct list *list, void (*data_destroy)(void *));

int list_is_empty(struct list *list);

struct list *list_nth_node(struct list *list, int n);

//pop out the node
struct list *list_pop(struct list *list, struct list *p);
//pop out the node with index as n
struct list *list_pop_by_index(struct list *list, int n);

//pop out the head node
struct list *list_pop_head(struct list *list);

//pop out the tail node
struct list *list_pop_tail(struct list *list);

//compare can be strcmp() or memcpy() or other self defined functions for
//comparing
struct list *list_find(struct list *list, struct list *key, int (*compare)(struct list*, struct list*));

int list_index(struct list *list, struct list *key);

struct list *list_replace(struct list *list, struct list *position, struct list *key);
struct list *list_replace_by_index(struct list *list, int n, struct list *key);

struct list *list_insert(struct list *list, struct list *key, struct list *position);
struct list *list_insert_by_index(struct list *list, struct list *key, int n);

struct list *list_insert_after(struct list *list, struct list *key, struct list *position);
struct list *list_insert_after_by_index(struct list *list, struct list *key, int n);

struct list *list_append(struct list *list, struct list *key);

struct list *list_push(struct list *list, struct list *key);

int list_remove(struct list *list, struct list *position, void (*data_destroy)(void *));
int list_remove_by_index(struct list *list, int n, void (*data_destroy)(void *));

int list_move(struct list *list, struct list *key, struct list *position);
int list_move_by_index(struct list *list, int a, int b);

int list_swap(struct list *list, struct list *x, struct list *y);
int list_swap_by_index(struct list *list, int a, int b);

//func is a callback function dealing with struct list::data
struct list *list_traverse(struct list *list, int (*visit)(struct list*, struct list *));
struct list *list_traverse_reverse(struct list *list, int (*visit)(struct list*, struct list *));

struct list *list_copy(struct list *lx, struct list *ly, int (*copy)(void *, void*));
struct list *list_revert(struct list *list);
struct list *list_merge(struct list *lx, struct list *ly);
struct list *list_split(struct list *lx, struct list *p);

struct list *list_mergesort(struct list *list, int (*compare)(void*, void*));

struct list *list_quicksort(struct list *list, int (*compare)(void*, void*));

#endif
