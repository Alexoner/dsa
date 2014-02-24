#include "linkedlist.h"
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stddef.h>
#include <string.h>
#include <assert.h>

struct list *node_new(void *data)
{
    struct list *node = malloc(sizeof(struct list));
    node->prev = node->next = NULL;
    return node;
}

struct list *node_new_int(int i)
{
    struct list *p = node_new(NULL);
    /*p->data = malloc(sizeof(int));*/
    /**(int*)p->data = i;*/
    return p;
}

struct list *node_new_num(double f)
{
    struct list *p = node_new(NULL);
    /*p->data = malloc(sizeof(double));*/
    /**(double*)p->data = f;*/
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

/*struct list *node_destroy(struct list *p, void* data_destroy(void*))*/
/*{*/
/*if (data_destroy)*/
/*{*/
/*data_destroy(p->data);*/
/*}*/
/*free(p);*/
/*return NULL;*/
/*}*/

struct list *list_init(struct list *list)
{
    if (!list)
    {
        list = (struct list*)malloc(sizeof(struct list) * 1);
    }
    memset(list, 0, sizeof(*list));
    return list;
}

struct list *list_destroy(struct list *list, void (*data_destroy)(void *))
{
    /*list_traverse(list, list_remove);*/
    /*struct list *p = NULL, *q;*/
    /*for (p = list->head; p; p = q)*/
    /*{*/
    /*q = p->next;*/
    /*list_remove(list, p, data_destroy);*/
    /*}*/
    /*list->head = list->tail = NULL;*/
    /*list->length = 0;*/
    return list;
}

int list_is_empty(struct list *list)
{
    /*return list->length == 0;*/
}

struct list *list_pop(struct list *list, struct list *p)
{
    struct list *prev = NULL, *next = NULL;

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
        /*list->head = next;*/
    }

    if (next)
    {
        next->prev = prev;
    }
    else
    {
        /*list->tail = prev;*/
    }

    p->next = p->prev = NULL;

    return p;

}

struct list *list_pop_by_index(struct list *list, int n)
{
    struct list *key = list_nth_node(list, n);
    return list_pop(list, key);
}

struct list *list_pop_head(struct list *list)
{
    struct list *p = NULL;
    /*p = list->head;*/
    /*if (p)*/
    /*{*/
    /*list->head = p->next;*/
    /*if (p->next)*/
    /*{*/
    /*p->next->prev = NULL;*/
    /*}*/
    /*else*/
    /*{*/
    /*list->tail = p->prev;*/
    /*}*/
    /*}*/
    return p;
}

struct list *list_pop_tail(struct list *list)
{
    struct list *p = NULL;
    /*p = list->tail;*/
    /*if (p)*/
    /*{*/
    /*list->tail = p->prev;*/
    /*if (p->prev)*/
    /*{*/
    /*p->prev->next = NULL;*/
    /*}*/
    /*else*/
    /*{*/
    /*list->head = NULL;*/
    /*}*/
    /*}*/
    return p;
}

/*int list_index(struct list *list, struct list *key)*/
/*{*/
/*int i = 0;*/
/*struct list *p = NULL;*/
/*for (p = list->head; p && p != key; p = p->next, i++);*/
/*if (!p)*/
/*{*/
/*return -1;*/
/*}*/
/*return i;*/
/*}*/

/*struct list *list_replace(struct list *list, struct list *old, struct list *new)*/
/*{*/
/*list_insert(list, new, old);*/
/*list_remove(list, old, free);*/
/*return new;*/
/*}*/

//insert node before position
/*struct list *list_insert(struct list *list, struct list *key, struct list *position)*/
/*{*/
/*assert(list);*/
/*assert(position);*/
/*struct list *prev = position->prev;*/

/*if (prev)*/
/*{*/
/*prev->next = key;*/
/*}*/
/*else*/
/*{*/
/*list->head = key;*/
/*}*/

/*position->prev = key;*/

/*key->prev = prev;*/
/*key->next = position;*/

/*list->length++;*/

/*return key;*/
/*}*/

struct list *list_insert_by_index(struct list *list, struct list *key, int n)
{
    struct list *p = list_nth_node(list, n);
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

/*struct list *list_insert_after(struct list *list, struct list *key, struct list *position)*/
/*{*/
/*assert(list);*/
/*assert(position);*/
/*struct list *next = position->next;*/
/*if (next)*/
/*{*/
/*key->next = next;*/
/*next->prev = key;*/
/*}*/
/*else*/
/*{*/
/*list->tail = key;*/
/*key->next = NULL;*/
/*}*/

/*position->next = key;*/
/*key->prev = position;*/

/*list->length++;*/

/*return key;*/
/*}*/

/*struct list *list_insert_after_by_index(struct list *list, struct list *key, int n)*/
/*{*/
/*assert(list);*/
/*struct list *p = list_nth_node(list, n);*/
/*list_insert_after(list, key, p);*/
/*return key;*/
/*}*/

/*struct list *list_append(struct list *list, struct list *node)*/
/*{*/
/*assert(list);*/
/*if (list->tail)*/
/*{*/
/*list_insert_after(list, node, list->tail);*/
/*}*/
/*else*/
/*{*/
/*list->tail = list->head = node;*/
/*}*/
/*return node;*/
/*}*/

int list_remove_by_index(struct list *list, int n, void (*data_destroy)(void *))
{
    struct list *p = list_nth_node(list, n);
    if (p)
    {
        return list_remove(list, p, data_destroy);
    }
    else
    {
        return -1;
    }
}

//move struct list *node before *position
/*int list_move(struct list *list, struct list *key, struct list *position)*/
/*{*/
/*struct list *prev = NULL;*/
/*struct list *next = NULL;*/

/*prev = key->prev;*/
/*next = key->next;*/

/*//"remove" node from the list*/
/*if (prev)*/
/*{*/
/*prev->next = next;*/
/*}*/
/*else*/
/*{*/
/*list->head = next;*/
/*}*/
/*if (next)*/
/*{*/
/*next->prev = prev;*/
/*}*/
/*else*/
/*{*/
/*list->tail = prev;*/
/*}*/

/*//insert node into the list,before position*/
/*if (position)*/
/*{*/
/*prev = position->prev;*/
/*if (prev)*/
/*{*/
/*prev->next = key;*/
/*}*/
/*else*/
/*{*/
/*list->head = key;*/
/*}*/

/*position->prev = key;*/

/*key->prev = prev;*/
/*key->next = position;*/
/*}*/
/*else*/
/*{*/
/*key->prev = list->tail;*/
/*key->next = NULL;*/
/*list->tail->next = key;*/
/*list->tail = key;*/
/*}*/
/*return 0;*/
/*}*/


//swap x and y in list
/*int list_swap(struct list *list, struct list *x, struct list *y)*/
/*{*/
/*struct list *ynext = NULL;*/
/*if (y->next)*/
/*{*/
/*//struct list *y has a node next to it*/
/*ynext = y->next;*/
/*}*/
/*else*/
/*{*/
/*//struct list *y doesn't have a node next to it,the last one*/
/*ynext = y->prev;*/
/*}*/
/*list_move(list, y, x);*/
/*if (ynext)*/
/*{*/
/*list_move(list, x, ynext);*/
/*}*/
/*else*/
/*{*/
/*list_move(list, x, NULL);*/
/*}*/
/*return 0;*/
/*}*/

/*int list_swap_by_index(struct list *list, int a, int b)*/
/*{*/
/*struct list *p, *q;*/
/*p = list_nth_node(list, a);*/
/*q = list_nth_node(list, b);*/
/*return list_swap(list, p, q);*/
/*}*/

/*struct list *list_traverse(struct list *list,*/
/*int (*visit)(struct list*, struct list *))*/
/*{*/
/*struct list *p = NULL;*/
/*int i;*/
/*for (i = 0, p = list->head; p; i++, p = p->next)*/
/*{*/
/*if (visit)*/
/*{*/
/*visit(list, p);*/
/*}*/
/*else*/
/*{*/
/*printf("%d:\t%p,%d\n", i, p, *(int*)(p->data));*/
/*[>printf("%d:\t%d\t", i, *(int*)(p->data));<]*/
/*}*/
/*}*/
/*if (!visit)*/
/*{*/
/*printf("\n\n");*/
/*}*/
/*return list;*/
/*}*/

/*struct list *list_traverse_reverse(struct list *list,*/
/*int (*visit)(struct list*, struct list *))*/
/*{*/
/*struct list *p = NULL;*/
/*int i;*/
/*for (i = 0, p = list->tail; p; i++, p = p->prev)*/
/*{*/
/*if (visit)*/
/*{*/
/*visit(list, p);*/
/*}*/
/*else*/
/*{*/
/*printf("%d:\t%p,%d\n", i, p, *(int*)(p->data));*/
/*[>printf("%d:\t%d\t", i, *(int*)(p->data));<]*/
/*}*/
/*}*/
/*if (!visit)*/
/*{*/
/*printf("\n\n");*/
/*}*/
/*return list;*/
/*}*/


/*struct list *list_copy(struct list *lx, struct list *ly,*/
/*int (*copy)(void *, void*))*/
/*{*/
/*struct list *p, *q;*/
/*[>for (p=)<]*/
/*return ly;*/
/*}*/
/*struct list *list_revert(struct list *list)*/
/*{*/
/*struct list *p, *q;*/
/*for (p = list->tail; p; p = q)*/
/*{*/
/*q = p->prev;*/
/*p->prev = p->next;*/
/*p->next = q;*/
/*}*/
/*p = list->head;*/
/*list->head = list->tail;*/
/*list->tail = p;*/
/*return list;*/
/*}*/



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

struct list *list_mergesort(struct list *list,
                            int (*compare)(void*, void*))
{

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

struct list *list_quicksort(struct list *list, int (*compare)(void*, void*))
{
    return list;
}


#ifdef TEST_CONTAINER


#endif
