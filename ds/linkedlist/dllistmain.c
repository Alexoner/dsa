#include "dlinkedlist.h"
#include <stdio.h>
#include <time.h>

int main()
{
    int i = 1000;
    Node *p = node_new(&i);
    long t;

    List *l = list_init(NULL);

    /*node_destroy(p, NULL);*/

    for (i = 0; i < 10; i++)
    {
        int *dp = (int*)malloc(sizeof(*dp));
        *dp = i;
        Node *key = node_new(dp);
        list_append(l, key);
    }

    for (i = 0; i < 5; i++)
    {
        int j = 7 * (i + 1);
        /*Node *q = node_new_int(i);*/
        Node q = {0, 0, 0};
        Node *node = node_new_int(j);
        q.data = &i;
        p = list_find(l, &q, NULL);
        q.data = &j;
        list_insert(l, p, node);
    }

    list_insert_by_index(l, 0, node_new_int(1992));
    list_insert_by_index(l, 15, node_new_int(311));
    list_append(l, node_new_int(611));
    list_move_by_index(l, 0, 5);
    list_remove_by_index(l, 8, free);
    list_remove_by_index(l, 0, free);
    list_remove_by_index(l, 611, free);
    list_remove_by_index(l, 15, free);
    /*list_traverse(l, NULL);*/
    /*list_move_by_index(l, 6, 7);*/
    list_move_by_index(l, 7, 8);
    list_swap_by_index(l, 6, 8);
    list_swap_by_index(l, 0, 14);
    list_swap_by_index(l, 1, 13);
    list_traverse(l, NULL);
    list_mergesort(l, NULL);
    list_traverse(l, NULL);
    list_destroy(l, free);
    list_traverse(l, NULL);

    t = time(NULL);
    srand(t);
    for (i = 0; i < 100000; i++)
    {
        p = node_new_int(rand() % 1000000);
        list_push(l, p);
    }
    printf("before merging:\n");
    for (i = 0; i < 100000; i++)
    {
        /*printf("%d\t", *(int*)list_nth_node(l, i)->data);*/
    }
    list_mergesort(l, NULL);
    list_traverse(l, NULL);
    list_traverse_reverse(l, NULL);
    list_revert(l);

    //this block of traversing the list is much slower than list_traverse(),
    //because it calls list_nth_node too many times
    for (i = 0; i < 100000; i++)
    {
        printf("%d\t", *(int*)list_nth_node(l, i)->data);
    }
    printf("time:%ld\n", time(NULL) - t);
    return 0;
}
