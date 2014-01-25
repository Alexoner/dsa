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
    int length;
    //int empty;
    Node *head;
    Node *tail;
    pthread_mutex_t lock; //mutex lock for thread safe
};

struct Node
{
    void *data;
    Node  *prev;
    Node *next;
};

Node *node_new(void *data);
Node *node_destroy(Node *p, void* data_destroy(void*));

List *list_init(List *list);

List *list_destroy(List *list);

int list_is_empty(List *list);

Node *list_nth_node(List *list, int n);

//pop out the node with index as n
Node *list_pop(List *list, int n);

//pop out the head node
Node *list_pop_head(List *list);

//pop out the tail node
Node *list_pop_tail(List *list);

Node *list_find(List *list, Node *key, int (*compare)(Node*, Node*));

int list_index(List *list, Node *key);

Node *list_replace(List *list, Node *position, Node *key);
Node *list_replace_by_index(List *list, int n, Node *key);

Node *list_insert(List *list, Node *position, Node *key);
Node *list_insert_by_index(List *list, int n, Node *key);

Node *list_insert_after(List *list, Node *position, Node *key);
Node *list_insert_after_by_index(List *list, int n, Node *key);

Node *list_append(List *list, Node *key);

int list_remove(List *list, Node *position);
int list_remove_by_index(List *list, int n);

int list_move(List *list, Node *position, Node *node);
int list_move_by_index(List *list, int a, int b);

int list_swap(List *list, Node *x, Node *y);
int list_swap_by_index(List *list, int a, int b);

List *list_traverse(List *list, int (*visit)(List*, Node *));

List *list_sort_merge(List *list, int (*compare)(Node*, Node*));

List *list_sort_bubble(List *list, int (*compare)(Node*, Node*));

#endif
