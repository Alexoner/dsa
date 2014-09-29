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
    int k = 0, i = 0;
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

    // count the length of loop
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

    // traverse to the start of the loop
    slow_p = head;
    for (i = 0, fast_p = head; i < k; i++)
        fast_p = fast_p->next;
    while (slow_p != fast_p)
    {
        slow_p = slow_p->next;
        fast_p = fast_p->next;
    }
    // fast_p==slow_p== start of the loop
    while (fast_p->next != slow_p)
    {
        fast_p = fast_p->next;
    }
    fast_p->next = NULL;
    return 1;
}

/* UTILITY FUNCTIONS */
/* Given a reference (pointer to pointer) to the head
  of a list and an int, pushes a new node on the front
  of the list. */
void push(struct node **head_ref, int new_data)
{
    /* allocate node */
    struct node *new_node = (struct node *)malloc(sizeof(struct node));

    /* put in the data  */
    new_node->data = new_data;

    /* link the old list off the new node */
    new_node->next = (*head_ref);

    /* move the head to point to the new node */
    (*head_ref) = new_node;
}

void printList(struct node *node)
{
    while (node)
    {
        printf("%d ", node->data);
        node = node->next;
    }
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
    head->next->next->next->next->next = head->next->next;

    detectAndRemoveLoop(head);

    printf("Linked list after removing: \n");
    printList(head);

    return 0;
}
