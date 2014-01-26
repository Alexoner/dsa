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

Node *node_new_int(int i)
{
    Node *p = node_new(NULL);
    p->data = malloc(sizeof(int));
    *(int*)p->data = i;
    return p;
}

Node *node_new_num(double f)
{
    Node *p = node_new(NULL);
    p->data = malloc(sizeof(double));
    *(double*)p->data = f;
    return p;
}

int compare_int(void *x, void *y)
{
    assert(x);
    assert(y);
    return *(int*)x - *(int*)y;
}

float compare_float(void *x, void *y)
{
    assert(x);
    assert(y);
    return *(float*)x - *(float*)y;
}

double compare_double(void *x, void *y)
{
    assert(x);
    assert(y);
    return *(double*)x - *(double*)y;
}

/*Node *node_destroy(Node *p, void* data_destroy(void*))*/
/*{*/
/*if (data_destroy)*/
/*{*/
/*data_destroy(p->data);*/
/*}*/
/*free(p);*/
/*return NULL;*/
/*}*/

List *list_init(List *list)
{
    if (!list)
    {
        list = (List*)malloc(sizeof(List) * 1);
    }
    memset(list, 0, sizeof(*list));
    return list;
}

List *list_destroy(List *list, void (*data_destroy)(void *))
{
    /*list_traverse(list, list_remove);*/
    Node *p = NULL, *q;
    for (p = list->head; p; p = q)
    {
        q = p->next;
        list_remove(list, p, data_destroy);
    }
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
    for (p = list->head; p && i < n; p = p->next, i++);
    return p;
}

Node *list_pop(List *list, Node *p)
{
    Node *prev = NULL, *next = NULL;

    if (!p)
    {
        return NULL;
    }

    prev = p->prev;
    next = p->next;

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

    p->next = p->prev = NULL;

    return p;

}

Node *list_pop_by_index(List *list, int n)
{
    Node *key = list_nth_node(list, n);
    return list_pop(list, key);
}

Node *list_pop_head(List *list)
{
    Node *p = NULL;
    p = list->head;
    if (p)
    {
        list->head = p->next;
        if (p->next)
        {
            p->next->prev = NULL;
        }
        else
        {
            list->tail = p->prev;
        }
    }
    return p;
}

Node *list_pop_tail(List *list)
{
    Node *p = NULL;
    p = list->tail;
    if (p)
    {
        list->tail = p->prev;
        if (p->prev)
        {
            p->prev->next = NULL;
        }
        else
        {
            list->head = NULL;
        }
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
    for (p = list->head; p && p != key; p = p->next, i++);
    if (!p)
    {
        return -1;
    }
    return i;
}

Node *list_replace(List *list, Node *old, Node *new)
{
    list_insert(list, new, old);
    list_remove(list, old, free);
    return new;
}

//insert node before position
Node *list_insert(List *list, Node *key, Node *position)
{
    assert(list);
    assert(position);
    Node *prev = position->prev;

    if (prev)
    {
        prev->next = key;
    }
    else
    {
        list->head = key;
    }

    position->prev = key;

    key->prev = prev;
    key->next = position;

    list->length++;

    return key;
}

Node *list_insert_by_index(List *list, Node *key, int n)
{
    Node *p = list_nth_node(list, n);
    if (p)
    {
        list_insert(list, key, p);
    }
    else
    {
        return NULL;
    }
    return key;
}

Node *list_insert_after(List *list, Node *key, Node *position)
{
    assert(list);
    assert(position);
    Node *next = position->next;
    if (next)
    {
        key->next = next;
        next->prev = key;
    }
    else
    {
        list->tail = key;
        key->next = NULL;
    }

    position->next = key;
    key->prev = position;

    list->length++;

    return key;
}

Node *list_insert_after_by_index(List *list, Node *key, int n)
{
    assert(list);
    Node *p = list_nth_node(list, n);
    list_insert_after(list, key, p);
    return key;
}

Node *list_append(List *list, Node *node)
{
    assert(list);
    if (list->tail)
    {
        list_insert_after(list, node, list->tail);
    }
    else
    {
        list->tail = list->head = node;
    }
    return node;
}

Node *list_push(List *list, Node *key)
{
    return list_append(list, key);
}

//remove position from list
int list_remove(List *list, Node *position, void (*data_destroy)(void *))
{
    assert(list);
    assert(position);
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

    if (data_destroy && position->data)
    {
        data_destroy(position->data);
    }
    free(position);
    list->length--;
    return 0;
}

int list_remove_by_index(List *list, int n, void (*data_destroy)(void *))
{
    Node *p = list_nth_node(list, n);
    if (p)
    {
        return list_remove(list, p, data_destroy);
    }
    else
    {
        return -1;
    }
}

//move Node *node before *position
int list_move(List *list, Node *key, Node *position)
{
    Node *prev = NULL;
    Node *next = NULL;

    prev = key->prev;
    next = key->next;

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
        list->tail = prev;
    }

    //insert node into the list,before position
    if (position)
    {
        prev = position->prev;
        if (prev)
        {
            prev->next = key;
        }
        else
        {
            list->head = key;
        }

        position->prev = key;

        key->prev = prev;
        key->next = position;
    }
    else
    {
        key->prev = list->tail;
        key->next = NULL;
        list->tail->next = key;
        list->tail = key;
    }
    return 0;
}

int list_move_by_index(List *list, int a, int b)
{
    Node *p, *q;
    p = list_nth_node(list, a);
    q = list_nth_node(list, b);
    return list_move(list, p, q);
}

//swap x and y in list
int list_swap(List *list, Node *x, Node *y)
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
    list_move(list, y, x);
    if (ynext)
    {
        list_move(list, x, ynext);
    }
    else
    {
        list_move(list, x, NULL);
    }
    return 0;
}

int list_swap_by_index(List *list, int a, int b)
{
    Node *p, *q;
    p = list_nth_node(list, a);
    q = list_nth_node(list, b);
    return list_swap(list, p, q);
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
            printf("%d:\t%p,%d\n", i, p, *(int*)(p->data));
            /*printf("%d:\t%d\t", i, *(int*)(p->data));*/
        }
    }
    if (!visit)
    {
        printf("\n\n");
    }
    return list;
}

List *list_traverse_reverse(List *list, int (*visit)(List*, Node *))
{
    Node *p = NULL;
    int i;
    for (i = 0, p = list->tail; p; i++, p = p->prev)
    {
        if (visit)
        {
            visit(list, p);
        }
        else
        {
            printf("%d:\t%p,%d\n", i, p, *(int*)(p->data));
            /*printf("%d:\t%d\t", i, *(int*)(p->data));*/
        }
    }
    if (!visit)
    {
        printf("\n\n");
    }
    return list;
}


List *list_copy(List *lx, List *ly, int (*copy)(void *, void*))
{
    Node *p, *q;
    /*for (p=)*/
    return ly;
}
List *list_revert(List *list)
{
    Node *p, *q;
    for (p = list->tail; p; p = q)
    {
        q = p->prev;
        p->prev = p->next;
        p->next = q;
    }
    p = list->head;
    list->head = list->tail;
    list->tail = p;
    return list;
}



/*************************************************************
 * LOOP/STACK BASED MERGE SORT to sort a linked list
 * **********************************************************
 *
 * Algorithm Description
 *
 * Mergesort takes the input list and treats it as a collection of small
 * sorted lists. It makes log N passes along the list, and in each pass it
 * combines each adjacent pair of small sorted lists into one larger sorted
 * list. When a pass only needs to do this once, the whole output list must
 * be sorted.
 *
 * So here's the algorithm. In each pass, we are merging lists of size K into
 * lists of size 2K. (Initially K equals 1.) So we start by pointing a
 * temporary pointer p at the head of the list, and also preparing an empty
 * list L which we will add elements to the end of as we finish dealing with
 * them. Then:
 *
 * If p is null, terminate this pass.
 * Otherwise, there is at least one element in the next pair of length-K
 * lists , so increment the number of merges performed in this pass.
 * Point another temporary pointer, q, at the same place as p. Step q along
 * the list by K places, or until the end of the list, whichever comes first.
 * Let psize be the number of elements you managed to step q past.
 * Let qsize equal K. Now we need to merge a list starting at p, of length
 * psize, with a list starting at q of length at most qsize.
 * So, as long as either the p-list is non-empty (psize > 0) or the q-list is
 * non-empty (qsize > 0 and q points to something non-null):
 * Choose which list to take the next element from. If either list is empty,
 * we must choose from the other one. (By assumption, at least one is
 * non-empty at this point.) If both lists are non-empty, compare the first
 * element of each and choose the lower one. If the first elements compare
 * equal, choose from the p-list. (This ensures that any two elements which
 * compare equal are never swapped, so stability is guaranteed.)
 * Remove that element, e, from the start of its list, by advancing p or q to
 * the next element along, and decrementing psize or qsize.
 * Add e to the end of the list L we are building up.
 * Now we have advanced p until it is where q started out, and we have
 * advanced q until it is pointing at the next pair of length-K lists to
 * merge. So set p to the value of q, and go back to the start of this loop.
 * As soon as a pass like this is performed and only needs to do one merge,
 * the algorithm terminates, and the output list L is sorted. Otherwise,
 * double the value of K, and go back to the beginning.
 *
 * This procedure only uses forward links, so it doesn't need a doubly linked
 * list. If it does have to deal with a doubly linked list, the only place
 * this matters is when adding another item to L.
 *
 * Dealing with a circularly linked list is also possible. You just have to
 * be * careful when stepping along the list. To deal with the ambiguity
 * between p==head meaning you've just stepped off the end of the list,
 * and p==head  meaning you've only just started, I usually use an
 * alternative form of the "step" operation: first step p to its successor
 * element, and then reset it to null if that step made it become equal to
 * the head of the list.
 * (You can quickly de-circularise a linked list by finding the second
 * element , and then breaking the link to it from the first, but this moves
 * the whole list round by one before the sorting process. This wouldn't
 * matter - we are about to sort the list, after all - except that it makes
 * the sort unstable.)
 * Complexity
 *
 * Like any self-respecting sort algorithm, this has running time O(N log N).
 * Because this is Mergesort, the worst-case running time is still
 * O(N log N);
 * there are no pathological cases.
 *
 * Auxiliary storage requirement is small and constant (i.e. a few variables
 * within the sorting routine). Thanks to the inherently different behaviour
 * of linked lists from arrays, this Mergesort implementation avoids the O(N)
 * auxiliary storage cost normally associated with the algorithm.
 */

List *list_mergesort(List *list, int (*compare)(void*, void*))
{
    Node *p = NULL, *q = NULL, *key = NULL;
    int i, listsize, nmerges, psize, qsize;
    listsize = 1;
    if (!compare)
    {
        compare = compare_int;
    }

    //merge N(log N) passes
    while (1)
    {
        //It makes log N passes along the list,(N = 2 ^ n)
        //and in each pass it combines each adjacent pair of
        //small sorted lists into one larger sorted list
        p = list->head;
        nmerges = 0;

        //merged along the list
        while (p)
        {
            //In each pass,
            //we are merging lists of size K into lists of size 2K.
            //(Initially K equals 1.
            psize = qsize = listsize;
            for (i = 0, q = p; i < listsize && q; i++, q = q->next);
            if (!q)
            {
                //finished a pass of merging the lists
                break;
            }

            /*printf("qsize: %d,x:%d,y:%d\n", qsize,*/
            /**(int*)p->data, *(int*)q->data);*/

            //merge two lists
            for (i = 0; psize || (qsize && q); i = 0)
            {
                if (!psize)
                {
                    key = q;
                    q = q->next;
                    qsize--;
                    i = 1;
                }
                else if (!qsize || !q)
                {
                    key = p;
                    p = p->next;
                    psize--;
                }
                else if (compare(p->data, q->data) <= 0)
                {
                    key = p;
                    p = p->next;
                    psize--;
                }
                else
                {
                    key = q;
                    q = q->next;
                    qsize--;
                    i = 1;
                }

                if (i && psize)
                {
                    list_move(list, key, p);
                    /*printf("moved:\n");*/
                    /*list_traverse(list, NULL);*/
                }
            }//merge two lists

            p = q;
            nmerges++;
        }//merged along the list

        /*printf("after merging list with size %d: \n", listsize);*/
        /*list_traverse(list, NULL);*/
        if (nmerges == 1 )
        {
            return list;
        }

        //doublize the listsize to merge
        listsize *= 2;
    }//merged a pass
}

/*quick sort the list*/
/**********************************************************************
 * ALGORITHM description
 *
 * The quick sort algorithm is considered the fastest sorting algorithm, and
 * the standard C library includes a quick sort function (qsort) but it works
 * on arrays, not linked lists. However, we can build an array holding
 * pointers to successive items in a linked list, use the qsort function and
 * then rebuild the linked list from the array of sorted pointers.
 */

List *list_quicksort(List *list, int (*compare)(void*, void*))
{
    return list;
}


#ifdef TEST_CONTAINER


#endif
