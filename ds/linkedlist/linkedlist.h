#ifndef DLINKEDLIST_H
#define DLINKEDLIST_H

#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

typedef struct List List;
typedef struct Node Node;

struct List
{
    int datasize;
    int length;
    //int empty;
    Node *head;
    Node *tail;
    pthread_mutex_t lock; //mutex lock for thread safe
};

struct dlist
{
    void *data;
    struct dlist  *prev;
    struct dlist *next;
};

Node *node_new(void *data);
Node *node_new_int(int i);
Node *node_new_num(double f);

int compare_int(void *x, void *y);
float compare_float(void *x, void *y);
double comare_double(void *x, void *y);

Node *node_destroy(Node *p, void* data_destroy(void*));

List *list_init(List *list);

List *list_destroy(List *list, void (*data_destroy)(void *));

int list_is_empty(List *list);

Node *list_nth_node(List *list, int n);

//pop out the node
Node *list_pop(List *list, Node *p);
//pop out the node with index as n
Node *list_pop_by_index(List *list, int n);

//pop out the head node
Node *list_pop_head(List *list);

//pop out the tail node
Node *list_pop_tail(List *list);

//compare can be strcmp() or memcpy() or other self defined functions for
//comparing
Node *list_find(List *list, Node *key, int (*compare)(Node*, Node*));

int list_index(List *list, Node *key);

Node *list_replace(List *list, Node *position, Node *key);
Node *list_replace_by_index(List *list, int n, Node *key);

Node *list_insert(List *list, Node *key, Node *position);
Node *list_insert_by_index(List *list, Node *key, int n);

Node *list_insert_after(List *list, Node *key, Node *position);
Node *list_insert_after_by_index(List *list, Node *key, int n);

Node *list_append(List *list, Node *key);

Node *list_push(List *list, Node *key);

int list_remove(List *list, Node *position, void (*data_destroy)(void *));
int list_remove_by_index(List *list, int n, void (*data_destroy)(void *));

int list_move(List *list, Node *key, Node *position);
int list_move_by_index(List *list, int a, int b);

int list_swap(List *list, Node *x, Node *y);
int list_swap_by_index(List *list, int a, int b);

//func is a callback function dealing with Node::data
List *list_traverse(List *list, int (*visit)(List*, Node *));
List *list_traverse_reverse(List *list, int (*visit)(List*, Node *));

List *list_copy(List *lx, List *ly, int (*copy)(void *, void*));
List *list_revert(List *list);
List *list_merge(List *lx, List *ly);
List *list_split(List *lx, Node *p);

List *list_mergesort(List *list, int (*compare)(void*, void*));

List *list_quicksort(List *list, int (*compare)(void*, void*));

#endif
