#include "dlinkedlist.h"
#include <stdio.h>

Node *node_new_int(int i)
{
    Node *p = node_new(NULL);
    p->data = malloc(sizeof(int));
    *(int*)p->data = i;
    return p;
}

int main()
{
    int i = 1000;
    Node *p = node_new(&i);

    printf("Node: %d\n", *(int*)p->data);
    List *l = list_init(NULL);

    node_destroy(p, NULL);

    for (i = 0; i < 10; i++)
    {
        int *dp = (int*)malloc(sizeof(*dp));
        *dp = i;
        Node *key = node_new(dp);
        list_append(l, key);
    }
    list_traverse(l, NULL);

    for (i = 0; i < 4; i++)
    {
        int j = 7 * i;
        /*Node *q = node_new_int(i);*/
        Node q = {0, 0, 0};
        Node *node = node_new_int(j);
        q.data = &i;
        p = list_find(l, &q, NULL);
        q.data = &j;
        list_insert(l, p, node);
    }
    list_traverse(l, NULL);
    return 0;
}
