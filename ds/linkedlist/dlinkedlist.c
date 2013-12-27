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
        node->prev = prev;
    }
    else
    {
        list->head = node;
        node->prev = NULL;
    }

    position->prev = node;
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

Node *list_remove(List *list, Node *position)
{
    Node *prev = position->prev;
    Node *next = position->next;

    if (prev)
    {
        prev->next = position->next;
    }
    else
    {
        list->head = position->next;
    }

    if (next)
    {
        next->prev = position->prev;
    }
    else
    {
        list->tail = position->prev;
    }

    free(position);

    list->length--;

    return position;
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
