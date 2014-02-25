#include "linkedlist.h"
#include <stdio.h>
#include <time.h>

typedef struct node Node;

struct node
{
    int a;
    struct list list;
};

Node *node_new(int i)
{
    Node *node = malloc(sizeof(Node));
    node->a = i;
    node->list.next = node->list.prev = NULL;
    /**node = {.a = i, .list = {NULL, NULL}};*/
    return node;
}

int node_compare(struct list *p, struct list *q, void *priv)
{
    Node *np, *nq;
    np = list_entry(p, Node, list);
    nq = list_entry(q, Node, list);
    return np->a - nq->a;
}

int node_visit(struct list *p, void *priv)
{
    printf("%d:\t%d\n",
           (*(int*)priv)++,
           list_entry(p, Node, list)->a);
    return 0;
}

int main()
{
    int i = 1000;
    Node *p;
    struct list *pl;
    long t;

    LIST_HEAD(l);

    /*node_destroy(p, NULL);*/

    for (i = 0; i < 10; i++)
    {
        /*int *dp = (int*)malloc(sizeof(*dp));*/
        /**dp = i;*/
        Node *key = node_new(i);
        list_append(&l, &(key->list));
    }

    i = 0;
    /*list_for_each(pl, &l)*/
    /*{*/
    /*printf("%d:\t%d\n", i, list_entry(pl, Node, list)->a);*/
    /*i++;*/
    /*}*/
    /*list_traverse(&l, node_visit, &i);*/
    putchar('\n');
    for (i = 0; i < 6; i++)
    {
        int j = 7 * (i + 1);
        /*Node *q = node_new_int(i);*/
        Node *q = node_new(0);
        Node *node = node_new(j);
        q->a = i;
        pl = list_find(&l, &q->list, node_compare, NULL);
        q = node_new(j);
        list_add(&node->list, pl);
    }


    i = 0;
    /*list_traverse(&l, node_visit, &i);*/
    putchar('\n');

    Node *node = node_new(1992);
    list_add_by_index(&l, &node->list, 0);
    node = node_new(311);
    list_add_by_index(&l, &node->list, 15);
    node = node_new(611);
    list_append(&l, &node->list);
    list_move_tail_by_index(&l, 5, &l, 0);
    /*list_for_each(pl, &l)*/
    /*{*/
    /*printf("%d:\t%d\n", i, list_entry(pl, Node, list)->a);*/
    /*i++;*/
    /*}*/
    i = 0;
    list_traverse(&l, node_visit, &i);
    putchar('\n');
    list_del_by_index(&l, 0);
    list_del_by_index(&l, 15);

    i = 0;
    list_traverse(&l, node_visit, &i);
    putchar('\n');

    /*list_move_by_index(l, 6, 7);*/
    list_move_by_index(&l, 7, &l, 8);
    list_swap_by_index(&l, 6, &l, 8);
    list_swap_by_index(&l, 0, &l, 14);
    list_swap_by_index(&l, 1, &l, 13);

    i = 0;
    list_traverse(&l, node_visit, &i);
    putchar('\n');

    list_mergesort(&l, node_compare, NULL);

    i = 0;
    list_traverse(&l, node_visit, &i);
    putchar('\n');

    /*list_traverse(&l, NULL, NULL);*/
    /*list_destroy(&l, free);*/
    /*list_traverse(&l, NULL);*/

    t = time(NULL);
    srand(t);
    for (i = 0; i < 100000; i++)
    {
        p = node_new(rand() % 1000000);
        /*list_push(&l, &p->list);*/
        /*list_add(&p->list, l.prev);*/
        list_add_by_index(&l, &p->list, 0);
    }

    printf("before merging:\n");

    i = 0;
    /*list_traverse(&l, node_visit, &i);*/
    i = 0;
    /*list_traverse_reverse(&l, node_visit, &i);*/
    putchar('\n');


    printf("After mergesort:\n");
    list_mergesort(&l, node_compare, NULL);

    i = 0;
    list_traverse(&l, node_visit, &i);
    putchar('\n');
    i = 0;
    list_traverse_reverse(&l, node_visit, &i);
    /*list_revert(l);*/

    //this block of traversing the list is much slower than list_traverse(),
    //because it calls list_nth_node too many times
    for (i = 0; i < 100000; i++)
    {
        /*printf("%d\t", *(int*)list_nth_node(l, i)->data);*/
    }
    printf("time:%ld\n", time(NULL) - t);
    return 0;
}
