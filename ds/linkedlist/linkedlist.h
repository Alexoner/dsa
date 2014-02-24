#ifndef DLINKEDLIST_H
#define DLINKEDLIST_H

#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

#include "../../dsadef.h"

//struct list
//{
//int datasize;
//int length;
////int empty;
//struct list *head;
//struct list *tail;
//pthread_mutex_t lock; //mutex lock for thread safe
//};



/*
 * Simple doubly linked list implementation.
 *
 * Some of the internal functions ("__xxx") are useful when
 * manipulating whole lists rather than single entries, as
 * sometimes we already know the next/prev entries and we can
 * generate better code by using them directly rather than
 * using the generic single-entry routines.
 */


struct list
{
    struct list  *prev;
    struct list *next;
};

#define LIST_HEAD_INIT(name) { &(name), &(name) }

#define LIST_HEAD(name) \
    struct list name = LIST_HEAD_INIT(name)

static inline void INIT_LIST_HEAD(struct list *list)
{
    list->next = list;
    list->prev = list;
}

/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
#ifndef CONFIG_DEBUG_LIST
static inline void __list_add(struct list *new,
                              struct list *prev,
                              struct list *next)
{
    next->prev = new;
    new->next = next;
    new->prev = prev;
    prev->next = new;
}
#else
extern void __list_add(struct list *new,
                       struct list *prev,
                       struct list *next);
#endif

/**
 * list_add - add a new entry
 * @new: new entry to be added
 * @head: list head to add it after
 *
 * Insert a new entry after the specified head.
 * This is good for implementing stacks.
 */
static inline void list_add(struct list *new, struct list *head)
{
    __list_add(new, head, head->next);
}


/**
 * list_add_tail - add a new entry
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
static inline void list_add_tail(struct list *new, struct list *head)
{
    __list_add(new, head->prev, head);
}

/*
 * Delete a list entry by making the prev/next entries
 * point to each other.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline void __list_del(struct list * prev, struct list * next)
{
    next->prev = prev;
    prev->next = next;
}

/**
 * list_del - deletes entry from list.
 * @entry: the element to delete from the list.
 * Note: list_empty() on entry does not return true after this, the entry is
 * in an undefined state.
 */
#ifndef CONFIG_DEBUG_LIST
static inline void list_del(struct list *entry)
{
    __list_del(entry->prev, entry->next);
    //entry->next = LIST_POISON1;
    //entry->prev = LIST_POISON2;
}
#else
extern void list_del(struct list *entry);
#endif

/**
 * list_replace - replace old entry by new one
 * @old : the element to be replaced
 * @new : the new element to insert
 *
 * If @old was empty, it will be overwritten.
 */
static inline void list_replace(struct list *old,
                                struct list *new)
{
    new->next = old->next;
    new->next->prev = new;
    new->prev = old->prev;
    new->prev->next = new;
}

static inline void list_replace_init(struct list *old,
                                     struct list *new)
{
    list_replace(old, new);
    INIT_LIST_HEAD(old);
}

/**
 * list_del_init - deletes entry from list and reinitialize it.
 * @entry: the element to delete from the list.
 */
static inline void list_del_init(struct list *entry)
{
    __list_del(entry->prev, entry->next);
    INIT_LIST_HEAD(entry);
}

/**
 * list_move - delete from one list and add as another's head
 * @list: the entry to move
 * @head: the head that will precede our entry
 *
 * if (list == head),because __list_del() doesn't changed the deleted
 * entry's prev and next pointer,so the list entry remains the same.
 */
static inline void list_move(struct list *list, struct list *head)
{
    __list_del(list->prev, list->next);
    list_add(list, head);
}

/**
 * list_move_tail - delete from one list and add as another's tail
 * @list: the entry to move
 * @head: the head that will follow our entry
 */
static inline void list_move_tail(struct list *list,
                                  struct list *head)
{
    __list_del(list->prev, list->next);
    list_add_tail(list, head);
}

/**
 * list_is_last - tests whether @list is the last entry in list @head
 * @list: the entry to test
 * @head: the head of the list
 */
static inline int list_is_last(const struct list *list,
                               const struct list *head)
{
    return list->next == head;
}

/**
 * list_empty - tests whether a list is empty
 * @head: the list to test.
 */
static inline int list_empty(const struct list *head)
{
    return head->next == head;
}

/**
 * list_empty_careful - tests whether a list is empty and not being modified
 * @head: the list to test
 *
 * Description:
 * tests whether a list is empty _and_ checks that no other CPU might be
 * in the process of modifying either member (next or prev)
 *
 * NOTE: using list_empty_careful() without synchronization
 * can only be safe if the only activity that can happen
 * to the list entry is list_del_init(). Eg. it cannot be used
 * if another CPU could re-list_add() it.
 */
static inline int list_empty_careful(const struct list *head)
{
    struct list *next = head->next;
    return (next == head) && (next == head->prev);
}

/**
 * list_is_singular - tests whether a list has just one entry.
 * @head: the list to test.
 */
static inline int list_is_singular(const struct list *head)
{
    return !list_empty(head) && (head->next == head->prev);
}

static inline void __list_cut_position(struct list *list,
                                       struct list *head,
                                       struct list *entry)
{
    struct list *new_first = entry->next;//first element of the new list
    list->next = head->next;
    list->next->prev = list;
    list->prev = entry;
    entry->next = list;
    head->next = new_first;//head remains to be list head,head->prev unchanged
    new_first->prev = head;
}

/**
 * list_cut_position - cut a list into two
 * @list: a new list to add all removed entries
 * @head: a list with entries
 * @entry: an entry within head, could be the head itself
 *  and if so we won't cut the list
 *
 * This helper moves the initial part of @head, up to and
 * including @entry, from @head to @list. You should
 * pass on @entry an element you know is on @head. @list
 * should be an empty list or a list you do not care about
 * losing its data.
 *
 */
static inline void list_cut_position(struct list *list,
                                     struct list *head, struct list *entry)
{
    if (list_empty(head))
        return;
    if (list_is_singular(head) &&
            (head->next != entry && head != entry))
        return;
    if (entry == head)
        INIT_LIST_HEAD(list);
    else
        __list_cut_position(list, head, entry);
}

/**
 * __list_splice - join two lists,this is designed for stacks
 * @list: the new list to add.
 * @prev: the place to add it after
 * @next: the place to add it before
 */
static inline void __list_splice(const struct list *list,
                                 struct list *prev,
                                 struct list *next)
{
    struct list *first = list->next;
    struct list *last = list->prev;

    first->prev = prev;
    prev->next = first;

    last->next = next;
    next->prev = last;
}

/**
 * list_splice - join two lists, this is designed for stacks
 * @list: the new list to add.
 * @head: the place to add it in the first list.
 */
static inline void list_splice(const struct list *list,
                               struct list *head)
{
    if (!list_empty(list))
        __list_splice(list, head, head->next);
}

/**
 * list_splice_tail - join two lists, each list being a queue
 * @list: the new list to add.
 * @head: the place to add it in the first list.
 */
static inline void list_splice_tail(struct list *list,
                                    struct list *head)
{
    if (!list_empty(list))
        __list_splice(list, head->prev, head);
}

/**
 * list_splice_init - join two lists and reinitialise the emptied list.
 * @list: the new list to add.
 * @head: the place to add it in the first list.
 *
 * The list at @list is reinitialised
 */
static inline void list_splice_init(struct list *list,
                                    struct list *head)
{
    if (!list_empty(list))
    {
        __list_splice(list, head, head->next);
        INIT_LIST_HEAD(list);
    }
}

/**
 * list_splice_tail_init - join two lists and reinitialise the emptied list
 * @list: the new list to add.
 * @head: the place to add it in the first list.
 *
 * Each of the lists is a queue.
 * The list at @list is reinitialised
 */
static inline void list_splice_tail_init(struct list *list,
        struct list *head)
{
    if (!list_empty(list))
    {
        __list_splice(list, head->prev, head);
        INIT_LIST_HEAD(list);
    }
}

/**
 * list_nth_node - the nth node in the list
 * @list: the list
 * @n: the index of the node,beginning with 0
 */
static inline struct list *list_nth_node(struct list *list, int n)
{
    int i = 0;
    struct list *p;
    for (p = list->next; i < n && p; i++, p = p->next);
    return p;
}

static inline struct list *list_find(struct list *list,
                                     struct list *key,
                                     int (*compare)(struct list*, struct list*, void *priv),
                                     void *priv)
{
    struct list *p = NULL;
    if (!compare)
    {
        return NULL;
    }
    for (p = list->next; p != list && compare(p, key, priv); p = p->next);
    return  p == list ? NULL : p;
}

/**
 * list_index - returns the index of an entry
 * @list: the list
 * @key: the entry
 *
 * index begins with 0
 */
static inline int list_index(struct list *list, struct list *key)
{
    int i;
    struct list *p;
    for (i = 0, p = list->next; p && p != key; i++, p = p->next);
    return i;
}

/**
 * list_replace_by_index - replace the nth entry of the list with the new one
 * @list: the list
 * @n: the index
 * @new: the new entry
 */
static inline struct list *list_replace_by_index(struct list *list,
        int n,
        struct list *new)
{
    struct list *old = list_nth_node(list, n);
    list_replace(old, new);
    return list;
}
/**
 * list_add_by_index - add a new entry by index
 * @list: list
 * @key: new entry to be added
 * @n: list head's index to add it after
 *
 * Insert a new entry after the specified head.
 * This is good for implementing stacks.
 */
static inline struct list *list_add_by_index(struct list *list,
        struct list *key,
        int n)
{
    list_add(key, list_nth_node(list, n));
    return list;
}

/**
 * list_add_tail_by_index - add a new entry by index
 * @list: list
 * @key: new entry to be added
 * @n: index of list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
static inline struct list *list_add_tail_by_index(struct list *list,
        struct list *key, int n)
{
    list_add_tail(key, list_nth_node(list, n));
    return list;
}

/**
 * list_append - add a new entry to a list's tail
 * @list: list
 * @key: new entry to be added
 *
 * Insert a new entry at a list's tail.
 * This is useful for implementing stacks and queues.
 */
static inline struct list *list_append(struct list *list,
                                       struct list *key)
{
    if (!list)
    {
        return NULL;
    }
    list_add(key, list->prev);
    return list;
}

/**
 * list_push - add a new entry to a list's tail
 * @list: list
 * @key: new entry to be added
 *
 * Insert a new entry at a list's tail.
 * This is useful for implementing stacks and queues.
 */
static inline struct list *list_push(struct list *list,
                                     struct list *key)
{
    if (!list)
    {
        return NULL;
    }
    list_add(key, list->prev);
    return list;
}

/**
 * list_del_by_index - deletes entry from list by index.
 * @list: the list
 * @n: the index of the element to be deleted
 * Note: list_empty() on entry does not return true after this, the entry is
 * in an undefined state.
 */
static inline int list_del_by_index(struct list *list,
                                    int n)
{
    list_del(list_nth_node(list, n));
    return 0;
}

/**
 * list_move_by_index - delete from one list and add as another's head
 * @list: the entry to move
 * @head: the head that will precede our entry
 *
 * if (list == head),because __list_del() doesn't changed the deleted
 * entry's prev and next pointer,so the list entry remains the same.
 */
static inline int list_move_by_index(struct list *list_from, int a,
                                     struct list *list_to, int b)
{
    list_move(list_nth_node(list_from, a), list_nth_node(list_to, b));
    return 0;
}

/**
 * list_move_tail_by_index - delete from one list and add as another's head
 * @list: the entry to move
 * @head: the head that will precede our entry
 *
 * if (list == head),because __list_del() doesn't changed the deleted
 * entry's prev and next pointer,so the list entry remains the same.
 */
static inline int list_move_tail_by_index(struct list *list_from,
        int a,
        struct list *list_to,
        int b)
{
    list_move_tail(list_nth_node(list_from, a), list_nth_node(list_to, b));
    return 0;
}

/**
 * list_swap - swap two entries
 * @x: an entry
 * @y: the other entry
 */
static inline int list_swap(struct list *x,
                            struct list *y)
{
    struct list *p;
    if (x->prev == y)
    {
        list_move(y, x);
    }
    else if (x->next == y)
    {
        list_move(x, y);
    }
    else
    {
        p = x->prev;
        list_move(x, y);
        list_move(y, p);
    }
    return 0;
}

static inline int list_swap_by_index(struct list *list_x, int a,
                                     struct list *list_y, int b)
{
    return list_swap(list_nth_node(list_x, a), list_nth_node(list_y, b));
}

/**
 * list_traverse - traverse a list
 * @list: the list to traverse
 * @visit: the callback function to be called for each entries in the list
 * @priv: private data, opaque to list_list_traverse(),passed to @visit
 */
static inline int *list_traverse(struct list *list,
                                 int (*visit)(struct list *, void *),
                                 void *priv)
{
    struct list *p = NULL;
    int i;
    for (i = 0, p = list->next; p && p != list; i++, p = p->next)
    {
        if (visit)
        {
            visit(p, priv);
        }
    }
    return 0;
}

static inline int *list_traverse_reverse(struct list *list,
        int (*visit)(struct list *, void *),
        void *priv)
{
    struct list *p = NULL;
    for (p = list->prev; p && p != list; p = p->prev)
    {
        if (visit)
        {
            visit(p, priv);
        }
    }
    return 0;
}

static inline struct list *list_copy(
    struct list *src, struct list *dest,
    int (*copy)(struct list *, void*))
{
    return dest;
}

static inline struct list *list_revert(struct list *src)
{
    struct list *p, *q;
    for (p = src; p != src; p = q)
    {
        q = p->next;
        p->next = p->prev;
        p->prev = q;
    }
    return src;
}

/**
 * list_merge - merge two list
 * @priv: private data,opaque
 * @cmp: callback function for comparing
 * @a: the one list not including list head
 * @b: the other list not including list head
 *
 * Returns a list organized in an intermediate format suited
 * to chaining of merge() calls: null-terminated, no reserved or
 * sentinel head node, "prev" links not maintained.The returned list does not
 * include a list head
 */
static struct list *list_merge(void *priv,
                               int (*cmp)(void *priv, struct list *a,
                                       struct list *b),
                               struct list *a, struct list *b)
{
    struct list head, *tail = &head;

    while (a && b)
    {
        /* if equal, take 'a' -- important for sort stability */
        if ((*cmp)(priv, a, b) <= 0)
        {
            tail->next = a;
            a = a->next;
        }
        else
        {
            tail->next = b;
            b = b->next;
        }
        tail = tail->next;
    }
    tail->next = a ? : b;
    return head.next;
}

/**
 * list_mergesort - merge sort a list
 * @list: the list to traverse
 * @visit: the callback function to be called for each entries in the list
 * @priv: private data, opaque to list_list_traverse(),passed to @visit
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
static inline struct list *list_mergesort(
    struct list *list,
    int (*compare)(struct list *, struct list*, void *),
    void *priv)
{
    struct list *p = NULL, *q = NULL, *key = NULL;
    int i, listsize, nmerges, psize, qsize;
    listsize = 1;
    if (!compare)
    {
        //compare = compare_int;
        return list;
    }

    //merge N(log N) passes
    while (1)
    {
        //It makes log N passes along the list,(N = 2 ^ n)
        //and in each pass it combines each adjacent pair of
        //small sorted lists into one larger sorted list
        p = list->next;
        nmerges = 0;

        //merged along the list
        while (p != list)
        {
            //In each pass,
            //we are merging lists of size K into lists of size 2K.
            //(Initially K equals 1.
            psize = qsize = listsize;

            //move q listsize entries after p
            for (i = 0, q = p; i < listsize && q != list;
                    i++, q = q->next);
            if (!q || q == list)
            {
                //finished a pass of merging the lists
                //printf("finished a passs of merging along the list\n");
                break;
            }

            /*printf("qsize: %d,x:%d,y:%d\n", qsize,*/
            /**(int*)p->data, *(int*)q->data);*/

            //merge two lists
            for (i = 0; psize || (qsize && (q != list)); i = 0)
            {
                if (!psize)
                {
                    key = q;
                    q = q->next;
                    qsize--;
                }
                else if (!qsize || !q)
                {
                    key = p;
                    p = p->next;
                    psize--;
                }
                else if (compare(p, q, priv) <= 0)
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

                if (i)
                {
                    list_move_tail(key, p);
                    //printf("After moving,list = %p,p = %p,q = %p\n",
                    //list, p, q);
                }
                //sleep(1);
                //printf("listsize: %d,psize: %d,qsize: %d.%d\n",
                //listsize, psize, qsize,
                //psize || (qsize && q));
            }//merge two lists

            p = q;
            nmerges++;
            printf("listsize: %d,nmerges: %d,p: %p,q: %p\n",
                   listsize, nmerges, p, q);
        }//have done merging along the list

        //printf("after merging list with size %d: \n", listsize);
        /*list_traverse(list, NULL);*/

        //when no merges are executed,indicating that listsize >=
        //the length of the list
        if (nmerges == 0 )
        {
            return list;
        }

        //doublize the listsize to merge
        listsize *= 2;
    }//merged a pass
    return list;
}

struct list *list_quicksort(struct list *list,
                            int (*compare)(struct list *, struct list*, void *priv));


/**
 * list_entry - get the struct for this entry
 * @ptr:    the &struct list pointer.
 * @type:   the type of the struct this is embedded in.
 * @member: the name of the list_struct within the struct.
 */
#define list_entry(ptr, type, member) \
    container_of(ptr, type, member)

/**
 * list_first_entry - get the first element from a list
 * @ptr:    the list head to take the element from.
 * @type:   the type of the struct this is embedded in.
 * @member: the name of the list_struct within the struct.
 *
 * Note, that list is expected to be not empty.
 */
#define list_first_entry(ptr, type, member) \
    list_entry((ptr)->next, type, member)

/**
 * list_for_each    -   iterate over a list
 * @pos:    the &struct list to use as a loop cursor.
 * @head:   the head for your list.
 */
#define list_for_each(pos, head) \
    for (pos = (head)->next; prefetch(pos->next), pos != (head); \
            pos = pos->next)

/**
 * __list_for_each  -   iterate over a list
 * @pos:    the &struct list to use as a loop cursor.
 * @head:   the head for your list.
 *
 * This variant differs from list_for_each() in that it's the
 * simplest possible list iteration code, no prefetching is done.
 * Use this for code that knows the list to be very short (empty
 * or 1 entry) most of the time.
 */
#define __list_for_each(pos, head) \
    for (pos = (head)->next; pos != (head); pos = pos->next)

/**
 * list_for_each_prev   -   iterate over a list backwards
 * @pos:    the &struct list to use as a loop cursor.
 * @head:   the head for your list.
 */
#define list_for_each_prev(pos, head) \
    for (pos = (head)->prev; prefetch(pos->prev), pos != (head); \
            pos = pos->prev)

/**
 * list_for_each_safe - iterate over a list safe against removal of list entry
 * @pos:    the &struct list to use as a loop cursor.
 * @n:      another &struct list to use as temporary storage
 * @head:   the head for your list.
 */
#define list_for_each_safe(pos, n, head) \
    for (pos = (head)->next, n = pos->next; pos != (head); \
        pos = n, n = pos->next)

/**
 * list_for_each_prev_safe - iterate over a list backwards safe against removal of list entry
 * @pos:    the &struct list to use as a loop cursor.
 * @n:      another &struct list to use as temporary storage
 * @head:   the head for your list.
 */
#define list_for_each_prev_safe(pos, n, head) \
    for (pos = (head)->prev, n = pos->prev; \
         prefetch(pos->prev), pos != (head); \
         pos = n, n = pos->prev)

/**
 * list_for_each_entry  -   iterate over list of given type
 * @pos:    the type * to use as a loop cursor.
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 */
#define list_for_each_entry(pos, head, member)              \
    for (pos = list_entry((head)->next, typeof(*pos), member);  \
         prefetch(pos->member.next), &pos->member != (head);    \
         pos = list_entry(pos->member.next, typeof(*pos), member))

/**
 * list_for_each_entry_reverse - iterate backwards over list of given type.
 * @pos:    the type * to use as a loop cursor.
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 */
#define list_for_each_entry_reverse(pos, head, member)          \
    for (pos = list_entry((head)->prev, typeof(*pos), member);  \
         prefetch(pos->member.prev), &pos->member != (head);    \
         pos = list_entry(pos->member.prev, typeof(*pos), member))

/**
 * list_prepare_entry - prepare a pos entry for use in list_for_each_entry_continue()
 * @pos:    the type * to use as a start point
 * @head:   the head of the list
 * @member: the name of the list_struct within the struct.
 *
 * Prepares a pos entry for use as a start point in list_for_each_entry_continue().
 */
#define list_prepare_entry(pos, head, member) \
    ((pos) ? : list_entry(head, typeof(*pos), member))

/**
 * list_for_each_entry_continue - continue iteration over list of given type
 * @pos:    the type * to use as a loop cursor.
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 *
 * Continue to iterate over list of given type, continuing after
 * the current position.
 */
#define list_for_each_entry_continue(pos, head, member)         \
    for (pos = list_entry(pos->member.next, typeof(*pos), member);  \
         prefetch(pos->member.next), &pos->member != (head);    \
         pos = list_entry(pos->member.next, typeof(*pos), member))

/**
 * list_for_each_entry_continue_reverse - iterate backwards from the given point
 * @pos:    the type * to use as a loop cursor.
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 *
 * Start to iterate over list of given type backwards, continuing after
 * the current position.
 */
#define list_for_each_entry_continue_reverse(pos, head, member)     \
    for (pos = list_entry(pos->member.prev, typeof(*pos), member);  \
         prefetch(pos->member.prev), &pos->member != (head);    \
         pos = list_entry(pos->member.prev, typeof(*pos), member))

/**
 * list_for_each_entry_from - iterate over list of given type from the current point
 * @pos:    the type * to use as a loop cursor.
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 *
 * Iterate over list of given type, continuing from current position.
 */
#define list_for_each_entry_from(pos, head, member)             \
    for (; prefetch(pos->member.next), &pos->member != (head);  \
         pos = list_entry(pos->member.next, typeof(*pos), member))

/**
 * list_for_each_entry_safe - iterate over list of given type safe against removal of list entry
 * @pos:    the type * to use as a loop cursor.
 * @n:      another type * to use as temporary storage
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 */
#define list_for_each_entry_safe(pos, n, head, member)          \
    for (pos = list_entry((head)->next, typeof(*pos), member),  \
        n = list_entry(pos->member.next, typeof(*pos), member); \
         &pos->member != (head);                    \
         pos = n, n = list_entry(n->member.next, typeof(*n), member))

/**
 * list_for_each_entry_safe_continue
 * @pos:    the type * to use as a loop cursor.
 * @n:      another type * to use as temporary storage
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 *
 * Iterate over list of given type, continuing after current point,
 * safe against removal of list entry.
 */
#define list_for_each_entry_safe_continue(pos, n, head, member)         \
    for (pos = list_entry(pos->member.next, typeof(*pos), member),      \
        n = list_entry(pos->member.next, typeof(*pos), member);     \
         &pos->member != (head);                        \
         pos = n, n = list_entry(n->member.next, typeof(*n), member))

/**
 * list_for_each_entry_safe_from
 * @pos:    the type * to use as a loop cursor.
 * @n:      another type * to use as temporary storage
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 *
 * Iterate over list of given type from current point, safe against
 * removal of list entry.
 */
#define list_for_each_entry_safe_from(pos, n, head, member)             \
    for (n = list_entry(pos->member.next, typeof(*pos), member);        \
         &pos->member != (head);                        \
         pos = n, n = list_entry(n->member.next, typeof(*n), member))

/**
 * list_for_each_entry_safe_reverse
 * @pos:    the type * to use as a loop cursor.
 * @n:      another type * to use as temporary storage
 * @head:   the head for your list.
 * @member: the name of the list_struct within the struct.
 *
 * Iterate backwards over list of given type, safe against removal
 * of list entry.
 */
#define list_for_each_entry_safe_reverse(pos, n, head, member)      \
    for (pos = list_entry((head)->prev, typeof(*pos), member),  \
        n = list_entry(pos->member.prev, typeof(*pos), member); \
         &pos->member != (head);                    \
         pos = n, n = list_entry(n->member.prev, typeof(*n), member))

/*
 * Double linked lists with a single pointer list head.
 * Mostly useful for hash tables where the two pointer list head is
 * too wasteful.
 * You lose the ability to access the tail in O(1).
 */

struct hlist_head
{
    struct hlist_node *first;
};

struct hlist_node
{
    struct hlist_node *next, **pprev;
};

#define HLIST_HEAD_INIT { .first = NULL }
#define HLIST_HEAD(name) struct hlist_head name = {  .first = NULL }
#define INIT_HLIST_HEAD(ptr) ((ptr)->first = NULL)
static inline void INIT_HLIST_NODE(struct hlist_node *h)
{
    h->next = NULL;
    h->pprev = NULL;
}

static inline int hlist_unhashed(const struct hlist_node *h)
{
    return !h->pprev;
}

static inline int hlist_empty(const struct hlist_head *h)
{
    return !h->first;
}

static inline void __hlist_del(struct hlist_node *n)
{
    struct hlist_node *next = n->next;
    struct hlist_node **pprev = n->pprev;
    *pprev = next;
    if (next)
        next->pprev = pprev;
}

static inline void hlist_del(struct hlist_node *n)
{
    __hlist_del(n);
    //n->next = LIST_POISON1;
    //n->pprev = LIST_POISON2;
}

static inline void hlist_del_init(struct hlist_node *n)
{
    if (!hlist_unhashed(n))
    {
        __hlist_del(n);
        INIT_HLIST_NODE(n);
    }
}

static inline void hlist_add_head(struct hlist_node *n, struct hlist_head *h)
{
    struct hlist_node *first = h->first;
    n->next = first;
    if (first)
        first->pprev = &n->next;
    h->first = n;
    n->pprev = &h->first;
}

/* next must be != NULL */
static inline void hlist_add_before(struct hlist_node *n,
                                    struct hlist_node *next)
{
    n->pprev = next->pprev;
    n->next = next;
    next->pprev = &n->next;
    *(n->pprev) = n;
}

static inline void hlist_add_after(struct hlist_node *n,
                                   struct hlist_node *next)
{
    next->next = n->next;
    n->next = next;
    next->pprev = &n->next;

    if (next->next)
        next->next->pprev  = &next->next;
}

/*
 * Move a list from one list head to another. Fixup the pprev
 * reference of the first entry if it exists.
 */
static inline void hlist_move_list(struct hlist_head *old,
                                   struct hlist_head *new)
{
    new->first = old->first;
    if (new->first)
        new->first->pprev = &new->first;
    old->first = NULL;
}

#define hlist_entry(ptr, type, member) container_of(ptr,type,member)

#define hlist_for_each(pos, head) \
    for (pos = (head)->first; pos && ({ prefetch(pos->next); 1; }); \
         pos = pos->next)

#define hlist_for_each_safe(pos, n, head) \
    for (pos = (head)->first; pos && ({ n = pos->next; 1; }); \
         pos = n)

/**
 * hlist_for_each_entry - iterate over list of given type
 * @tpos:   the type * to use as a loop cursor.
 * @pos:    the &struct hlist_node to use as a loop cursor.
 * @head:   the head for your list.
 * @member: the name of the hlist_node within the struct.
 */
#define hlist_for_each_entry(tpos, pos, head, member)            \
    for (pos = (head)->first;                    \
         pos && ({ prefetch(pos->next); 1;}) &&          \
        ({ tpos = hlist_entry(pos, typeof(*tpos), member); 1;}); \
         pos = pos->next)

/**
 * hlist_for_each_entry_continue - iterate over a hlist continuing after current point
 * @tpos:   the type * to use as a loop cursor.
 * @pos:    the &struct hlist_node to use as a loop cursor.
 * @member: the name of the hlist_node within the struct.
 */
#define hlist_for_each_entry_continue(tpos, pos, member)         \
    for (pos = (pos)->next;                      \
         pos && ({ prefetch(pos->next); 1;}) &&          \
        ({ tpos = hlist_entry(pos, typeof(*tpos), member); 1;}); \
         pos = pos->next)

/**
 * hlist_for_each_entry_from - iterate over a hlist continuing from current point
 * @tpos:   the type * to use as a loop cursor.
 * @pos:    the &struct hlist_node to use as a loop cursor.
 * @member: the name of the hlist_node within the struct.
 */
#define hlist_for_each_entry_from(tpos, pos, member)             \
    for (; pos && ({ prefetch(pos->next); 1;}) &&            \
        ({ tpos = hlist_entry(pos, typeof(*tpos), member); 1;}); \
         pos = pos->next)

/**
 * hlist_for_each_entry_safe - iterate over list of given type safe against removal of list entry
 * @tpos:   the type * to use as a loop cursor.
 * @pos:    the &struct hlist_node to use as a loop cursor.
 * @n:      another &struct hlist_node to use as temporary storage
 * @head:   the head for your list.
 * @member: the name of the hlist_node within the struct.
 */
#define hlist_for_each_entry_safe(tpos, pos, n, head, member)        \
    for (pos = (head)->first;                    \
         pos && ({ n = pos->next; 1; }) &&               \
        ({ tpos = hlist_entry(pos, typeof(*tpos), member); 1;}); \
         pos = n)


int compare_int(void *x, void *y);
float compare_float(void *x, void *y);
double compare_double(void *x, void *y);

struct list *node_destroy(struct list *p, void* data_destroy(void*));


//pop out the head node
struct list *list_pop_head(struct list *list);

//pop out the tail node
struct list *list_pop_tail(struct list *list);

//compare can be strcmp() or memcpy() or other self defined functions for
//comparing


//struct list *list_replace(struct list *list, struct list *position, struct list *key);



int list_remove(struct list *list, struct list *position, void (*data_destroy)(void *));

//int list_move(struct list *list, struct list *key, struct list *position);


//func is a callback function dealing with struct list::data


#endif






