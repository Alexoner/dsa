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
                                       struct list *head, struct list *entry)
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
                                     int (*compare)(struct list*, struct list*));

static inline int list_index(struct list *list, struct list *key)
{
    int i;
    struct list *p;
    for (i = 0, p = list->next; p && p != key; i++, p = p->next);
    return i;
}

static inline struct list *list_replace_by_index(struct list *list,
        int n,
        struct list *new)
{
    struct list *old = list_nth_node(list, n);
    list_replace(old, new);
    return list;
}

static inline struct list *list_add_by_index(struct list *list,
        struct list *key,
        int n)
{
    list_add(key, list_nth_node(list, n));
    return list;
}

struct list *list_add_tail_by_index(struct list *list, struct list *key, int n);
struct list *list_append(struct list *list, struct list *key);
struct list *list_push(struct list *list, struct list *key);
int list_del_by_index(struct list *list, int n, void (*data_destroy)(void *));
int list_move_by_index(struct list *list, int a, int b);
int list_swap(struct list *list, struct list *x, struct list *y);
int list_swap_by_index(struct list *list, int a, int b);

struct list *list_traverse(struct list *list, int (*visit)(struct list*, struct list *));
struct list *list_traverse_reverse(struct list *list, int (*visit)(struct list*, struct list *));

struct list *list_copy(struct list *lx, struct list *ly, int (*copy)(void *, void*));
struct list *list_revert(struct list *list);
struct list *list_mergesort(struct list *list, int (*compare)(void*, void*));

struct list *list_quicksort(struct list *list, int (*compare)(void*, void*));

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

struct list *list_insert(struct list *list, struct list *key, struct list *position);

struct list *list_insert_after(struct list *list, struct list *key, struct list *position);



int list_remove(struct list *list, struct list *position, void (*data_destroy)(void *));

//int list_move(struct list *list, struct list *key, struct list *position);


//func is a callback function dealing with struct list::data

struct list *list_merge(struct list *lx, struct list *ly);

#endif
