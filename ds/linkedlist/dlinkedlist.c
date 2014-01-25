#include "dlinkedlist.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stddef.h>
#include <string.h>
#include <assert.h>

Node *node_new(void *data)
{
    Node *node = malloc(sizeof(Node));
    node->data = data;
    node->prev = node->next = NULL;
    return node;
}

Node *node_destroy(Node *p, void* data_destroy(void*))
{
    if (data_destroy)
    {
        data_destroy(p->data);
    }
    free(p);
    return NULL;
}

List *list_init(List *list)
{
    if (!list)
    {
        list = (List*)malloc(sizeof(List) * 1);
    }
    memset(list, 0, sizeof(*list));
    return list;
}

List *list_destroy(List *list)
{
    list_traverse(list, list_remove);
    list->head = list->tail = NULL;
    list->length = 0;
    return list;
}

int list_is_empty(List *list)
{
    return list->length == 0;
}

Node *list_nth_node(List *list, int n)
{
    //n counts from 0
    Node *p = NULL;
    int i = 0;
    for (p = list->head; p && i < n; p = p->next);
    if (!p)
    {
        return NULL;
    }
    return p;
}

Node *list_find(List *list, Node *key, int (*compare)(Node*, Node*))
{
    Node *p = NULL;
    for (p = list->head; p; p = p->next)
    {
        if (compare)
        {
            if (!compare(p, key))
            {
                return p;
            }
        }
        else
        {
            //compare function is NULL pointer,compare as integers
            if (!((*(int*)p->data) - (*(int*)key->data)))
            {
                return p;
            }
        }
    }
    return NULL;
}

int list_index(List *list, Node *key)
{
    int i = 0;
    Node *p = NULL;
    for (p = list->head; p; p = p->next, i++)
    {

    }
    return 0;
}

Node *list_replace(List *list, Node *position, Node *key)
{
    return key;
}

//insert node before position
Node *list_insert(List *list, Node *position, Node *node)
{
    Node *prev = position->prev;

    if (prev)
    {
        prev->next = node;
    }
    else
    {
        list->head = node;
    }

    position->prev = node;

    node->prev = prev;
    node->next = position;

    list->length++;

    return node;
}

Node *list_insert_after(List *list, Node *position, Node *node)
{
    assert(position);
    Node *next = position->next;
    if (next)
    {
        node->next = next;
        next->prev = node;
    }
    else
    {
        list->tail = node;
        node->next = NULL;
    }

    position->next = node;
    node->prev = position;

    list->length++;

    return node;
}

Node *list_append(List *list, Node *node)
{
    if (list->tail)
    {
        list_insert_after(list, list->tail, node);
    }
    else
    {
        list->tail = list->head = node;
    }
    return node;
}

//remove position from list
int list_remove(List *list, Node *position)
{
    Node *prev = position->prev;
    Node *next = position->next;

    if (prev)
    {
        prev->next = next;
    }
    else
    {
        list->head = next;
    }

    if (next)
    {
        next->prev = prev;
    }
    else
    {
        list->tail = prev;
    }

    free(position);

    list->length--;

    return 0;
}

//move Node *node before *position
Node *list_move(List *list, Node *position, Node *node)
{
    Node *prev = NULL;
    Node *next = NULL;

    prev = node->prev;
    next = node->next;

    //"remove" node from the list
    if (prev)
    {
        prev->next = next;
    }
    else
    {
        list->head = next;
    }
    if (next)
    {
        next->prev = prev;
    }
    else
    {
        list->tail = NULL;
    }

    //insert node into the list,before position
    prev = position->prev;

    if (prev)
    {
        prev->next = node;
    }
    else
    {
        list->head = node;
    }

    position->prev = node;

    node->prev = prev;
    node->next = position;

    return node;
}

//swap x and y in list
List *list_swap(List *list, Node *x, Node *y)
{
    Node *ynext = NULL;
    if (y->next)
    {
        //Node *y has a node next to it
        ynext = y->next;
    }
    /*else*/
    /*{*/
    /*//Node *y doesn't have a node next to it,the last one*/
    /*ynext = y->prev;*/
    /*}*/
    list_move(list, x, y);
    if (ynext)
    {
        list_move(list, x, ynext);
    }
    else
    {
        list_append(list, x);
    }
    return list;
}

List *list_traverse(List *list, int (*visit)(List*, Node *))
{
    Node *p = NULL;
    int i;
    for (i = 0, p = list->head; p; i++, p = p->next)
    {
        if (visit)
        {
            visit(list, p);
        }
        else
        {
            printf("%d: %p,%d\n", i, p, *(int*)(p->data));
        }
    }
    if (!visit)
    {
        printf("\n");
    }
    return list;
}

/*************************************************************
 * use STACK BASED MERGE SORT to sort a linked list
 * **********************************************************/
List *list_sort_merge(List *list, int (*compare)(Node*, Node*))
{
    return list;
}

/*Bubble sort the list*/
List *list_sort_bubble(List *list, int (*compare)(Node*, Node*))
{
    return list;
}


#ifdef TEST_CONTAINER
int main()
{
    List a;
    return 0;
}

#endif
