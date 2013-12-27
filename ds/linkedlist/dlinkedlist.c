#include "dlinkedlist.h"
#include <stdlib.h>
#include <unistd.h>
#include <stddef.h>
#include <string.h>

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

Node *list_locate_node(List *list, Node *key, int (*compare)(Node*, Node*))
{
    Node *p = NULL;
    for (p = list->head; p; p = p->next)
    {
        if (!compare(p, key))
        {
            return p;
        }
    }
    return NULL;
}

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
    list_insert_after(list, list->tail, node);
    return node;
}

Node *list_remove(List *list, Node *position)
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

    return position;
}

//insert Node *node before *position
Node *list_move(List *list, Node *position, Node *node)
{
    Node *prev = NULL;
    Node *next = NULL;

    prev = node->prev;
    next = node->next;

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

    prev = position->prev;
    next = position->next;

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

list *list_swap(List *list, Node *x, Node *y)
{
    Node *ynext = NULL;
    if (y->next)
    {
        //Node *y has a node next to it
        ynext = y->next;
    }
    else
    {
        //Node *y doesn't have a node next to it,the last one
        ynext = y->prev;
    }
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
    for (p = list->head; p; p = p->next)
    {
        visit(list, p);
    }
    return list;
}

List *list_sort(List *list, int (*compare)(Node *, Node *));
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
