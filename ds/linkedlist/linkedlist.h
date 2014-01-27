#ifndef DLINKEDLIST_H
#define DLINKEDLIST_H

#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

typedef struct list List;
typedef struct Node Node;

//struct list
//{
//int datasize;
//int length;
////int empty;
//Node *head;
//Node *tail;
//pthread_mutex_t lock; //mutex lock for thread safe
//};

struct list
{
    void *data;
    struct list  *prev;
    struct list *next;
};

Node *node_new(void *data);
Node *node_new_int(int i);
Node *node_new_num(double f);

int compare_int(void *x, void *y);
float compare_float(void *x, void *y);
double comare_double(void *x, void *y);

Node *node_destroy(Node *p, void* data_destroy(void*));

struct list *list_init(struct list *list);

struct list *list_destroy(struct list *list, void (*data_destroy)(void *));

int list_is_empty(struct list *list);

struct list *list_nth_node(struct list *list, int n);

//pop out the node
Node *list_pop(struct list *list, Node *p);
//pop out the node with index as n
Node *list_pop_by_index(struct list *list, int n);

//pop out the head node
Node *list_pop_head(struct list *list);

//pop out the tail node
Node *list_pop_tail(struct list *list);

//compare can be strcmp() or memcpy() or other self defined functions for
//comparing
Node *list_find(struct list *list, Node *key, int (*compare)(Node*, Node*));

int list_index(struct list *list, Node *key);

Node *list_replace(struct list *list, Node *position, Node *key);
Node *list_replace_by_index(struct list *list, int n, Node *key);

Node *list_insert(struct list *list, Node *key, Node *position);
Node *list_insert_by_index(struct list *list, Node *key, int n);

Node *list_insert_after(struct list *list, Node *key, Node *position);
Node *list_insert_after_by_index(struct list *list, Node *key, int n);

Node *list_append(struct list *list, Node *key);

Node *list_push(struct list *list, Node *key);

int list_remove(struct list *list, Node *position, void (*data_destroy)(void *));
int list_remove_by_index(struct list *list, int n, void (*data_destroy)(void *));

int list_move(struct list *list, Node *key, Node *position);
int list_move_by_index(struct list *list, int a, int b);

int list_swap(struct list *list, Node *x, Node *y);
int list_swap_by_index(struct list *list, int a, int b);

//func is a callback function dealing with Node::data
struct list *list_traverse(struct list *list, int (*visit)(struct list*, Node *));
struct list *list_traverse_reverse(struct list *list, int (*visit)(struct list*, Node *));

struct list *list_copy(struct list *lx, struct list *ly, int (*copy)(void *, void*));
struct list *list_revert(struct list *list);
struct list *list_merge(struct list *lx, struct list *ly);
struct list *list_split(struct list *lx, Node *p);

struct list *list_mergesort(struct list *list, int (*compare)(void*, void*));

struct list *list_quicksort(struct list *list, int (*compare)(void*, void*));

#endif
