/*
 * Detect loop in a linked list
 *
 * Hashing
 *
 * Mark visited Nodes
 *
 * Folyd's Cycle-Finding Algorithm,
 * also called the "tortoise and the hare" algorithm,is a pointer algorithm
 * that uses only two pointers,which move through the sequence at different
 * speeds.
 * This is the fastest method.Traverse linked list using two pointers.Move
 * one pointer by one and other pointer by two.If these pointers meet at
 *
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include "../linkedlist.h"

struct node
{
    int data;
    struct node *next;
};

void push(struct node **head, int data)
{
    // allocate node
    struct node *new_node = (struct node *)malloc(sizeof(struct node));

    new_node->data = data;

    new_node->next = (*head);

    (*head) = new_node;
}

int detectLoop(struct node *head)
{
    struct node *slow_p = head, *fast_p = head;
    while (slow_p && fast_p && fast_p->next)
    {
        slow_p = slow_p->next;
        fast_p = fast_p->next->next;
        if (slow_p == fast_p)
        {
            printf("Found loop\n");
            return 1;
        }
    }

    return 0;
}

int main(int argc, char **argv)
{
    struct node *head = NULL;
    push(&head, 20);
    push(&head, 4);
    push(&head, 15);
    push(&head, 10);

    head->next->next->next->next = head;
    detectLoop(head);

    return 0;
}
