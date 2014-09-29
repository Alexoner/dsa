/*
 * Detect and Remove loop in a linked list
 *
 * Method 1(Check one by one)
 *
 * Method 2(Efficient Solution)
 * Dependent on Floyd's Cycle detection algorithm.
 * 1)Detect Loop using Floyd's Cycle detection and get the pointer to a loop
 * node.
 * 2)Count the number of nodes in loop.Let the count be k.
 * 3)Fix one pointer to the head and another to kth node from head.
 * 4)Move both pointers at the same pace,they will meet at loop starting
 * node.
 * 5)Get pointer to the last node of loop and make next of it as NULL.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Linked list node*/
struct node
{
    int data;
    struct node *next;
};

int detectAndRemoveLoop(struct node *head)
{
    int k = 0;
    struct node *slow_p = NULL, *fast_p = NULL;

    // detect loop
    slow_p = fast_p = head;
    while (slow_p && fast_p && fast_p->next)
    {
        slow_p = slow_p->next;
        fast_p = fast_p->next->next;
        if (slow_p == fast_p)
        {
            break;
        }
    }

    if (slow_p == fast_p)
    {
        // loop exists
        k = 0;
        do
        {
            fast_p = fast_p->next;
            k++;
        } while (slow_p != fast_p);
    }
    else
    {
        return 0;
    }
    return 1;
}

// driver program
int main(int argc, char **argv)
{
    struct node *head = NULL;

    push(&head, 10);
    push(&head, 4);
    push(&head, 15);
    push(&head, 20);
    push(&head, 50);

    // create a loop
    head->next->next->next->next = head->next->next;

    detectAndRemoveLoop(head);

    printf("Linked list after removing: \n");
    printList(head);

    return 0;
}
