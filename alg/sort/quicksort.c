#include "../define.h"
#include "../utils.h"
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

/*****************************************************
 * DIVIDE:RECURSE,STACK.
 * CONQUER:SWAP
 * COMBINE:DONE
 * **************************************************/

#pragma mark - partition alorithms

//basic quick sort with recursion, this is the Lumoto verion
int partition(int *a, int p, int r)
{
    int pivot = a[r];
    int i, j;
    /*A[i] points to element not greater than pivot*/
    /*A[i + 1] points to element greater than pivot*/
    for (i = p - 1, j = p; j < r; j++)
    {
        if (a[j] <= pivot)
        {
            i++;
            SWAP(a[i], a[j], int);
        }
    }
    SWAP(a[r], a[i + 1], int);
    return i + 1;
}

// Origianl Hoare version of partition, which scans from two ends
//instead of one end
void quicksortHoare(int *a, int p, int r)
{
    int i, j, key, tmp;
    key = a[p];
    i = p;
    j = r;
    if (p >= r)
        return ;
    while (1)
    {
        for (; key >= a[i] && i < r; i++); //looking for number >key
        for (; a[j] >= key && j > p; j--); //for number<key,
        if (i < j)
        {
            tmp = a[i];
            a[i] = a[j];
            a[j] = a[i];
        }
        else
            break;
    }
    tmp = a[j];
    a[j] = a[p];
    a[p] = tmp; //so,the array is divided into two by key
    quicksortHoare(a, p, j - 1);
    quicksortHoare(a, j + 1, r);
}

//partition with equal elements
// three-way partition(Dutch National Flag problem)
int three_way_partition(int *a, int p, int r)
{
    // TODO: bug
    int i = p - 1, j = p, k;
    int pivot = a[r];
    int q;
    for (; j < r; j++)
    {
        if ( a[j] < pivot)
        {
            i++;
            SWAP(a[j], a[i], int);
            for (k = i - 1; k > p && a[k] == pivot; k--)
            {
                SWAP(a[k + 1], a[k], int);
            }
        }
        else if (a[j] == pivot)
        {
            i++;
            SWAP(a[j], a[i], int);
        }
    }

    q = i + 1;
    SWAP(a[r], a[q], int);
    return q;
}

//quick sort with randomization
int randomized_partition(int *a, int p, int r)
{
    /*srand(time(NULL));*/
    int i = rand() % (r - p + 1);
    SWAP(a[r], a[p + i], int);
    return partition(a, p, r);
}

#pragma mark - quick sort

void quicksort(int *a, int p, int r)
{
    if (p < r)
    {
        int q = partition(a, p, r);
        quicksort(a, p, q - 1);
        quicksort(a, q + 1, r);
    }
}

void randomized_quicksort(int *a, int p, int r)
{
    if (p < r)
    {
        int q = randomized_partition(a, p, r);
        randomized_quicksort(a, p, q - 1);
        randomized_quicksort(a, q + 1, r);
    }
}

//TODO: quick sort with stack instead of recursion

//tail recursion quicksort
void quicksort_tail_recursion(int *a, int p, int r)
{
    int q;
    while (p < r)
    {
        q = partition(a, p, r);
        quicksort_tail_recursion(a, p, q - 1);
        p = q + 1;
    }
}

#pragma mark - quick sort with repeated/equal elements

#define EXCHANGE(a, b) tmp = a; a = b; b = tmp;

typedef struct {
    int q;
    int t;
} pivot_t;

pivot_t partition_equal(int[], int, int);
pivot_t randomized_partition_equal(int[], int, int);

void quicksort_equal(int A[], int p, int r) {
    if (p < r - 1) {
        pivot_t pivot = randomized_partition_equal(A, p, r);
        quicksort_equal(A, p, pivot.q);
        quicksort_equal(A, pivot.t, r);
    }
}

pivot_t randomized_partition_equal(int A[], int p, int r) {
    int i = rand() % (r - p) + p,
        tmp;

    EXCHANGE(A[i], A[r-1]);

    return partition_equal(A, p, r);
}

pivot_t partition_equal(int A[], int p, int r) {
    int x = A[r - 1],
        q = p,
        t,
        tmp;

    for (int i = p; i < r - 1; i++) {
        if (A[i] < x) {
            EXCHANGE(A[q], A[i]);
            q++;
        }
    }

    for (t = q; t < r && A[t] == x; t++);

    for (int i = r - 1; i >= t; i--) {
        if (A[i] == x) {
            EXCHANGE(A[t], A[i]);
            t++;
        }
    }

    pivot_t result = {q, t};
    return result;
}

#pragma mark - main


int main()
{
    int n, i;
    /*printf("please how mant numbers you want to input\n");*/
    /*if (!scanf("%d", &n))*/
    /*exit(0);*/
    /*int a[n];*/
    /*printf("now plese input the numbers\n");*/
    /*i = 0;*/
    /*while (i < n && scanf("%d", a + i))*/
    /*i++;*/
    /*for (i = 0; i < n; i++)*/
    /*printf("%d", a[i]);*/
    /*printf("\n");*/
    /*quicksort(a, 0, n - 1);*/
    /*for (i = 0; i < n; i++)*/
    /*printf("%d  ", a[i]);*/
    /*printf("\n");*/

    n = 100;
    int a[n];
    srand(time(NULL));
    for (i = 0; i < n; i++)
    {
        /*a[i] = rand() % 1000000;*/
        a[i] = rand() % 100;
    }
    /*randomized_quicksort(a, 0, n - 1);*/
    quicksort_equal(a, 0, n - 1);
    for (i = 0; i < n; i++)
    {
        printf("%d\t", a[i]);
    }
    printf("\n");
    return 0;
}
