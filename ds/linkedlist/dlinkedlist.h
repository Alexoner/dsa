#ifndef DLINKEDLIST_H
#define DLINKEDLIST_H

typedef struct List List;
typedef struct Node Node;

struct List
{
    int length;
    Node *head;
    Node *tail;
};

struct Node
{
    void *data;
    Node  *prev;
    Node *next;
};

#endif
