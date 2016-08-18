// C program to show segment tree operations like construction, query
// and update
#include <math.h>
#include <stdio.h>

// A recursive function that constructs Segment Tree for array[ss..se].
// si is index of current node in segment tree st
int constructSTRecursion(int* st, int* arr, int ss, int se, int si)
{
    //printf("ss: %d, se: %d\n", ss, se);
    // If there is one element in array, store it in current node of
    // segment tree and return
    if (ss == se) {
        st[si] = arr[ss];
    } else {
        // If there are more than one elements, then recur for left and
        // right subtrees and store the sum of values in this node
        int mid = (ss + se) >> 1;
        int left = 2 * si + 1;
        int right = 2 * si + 2;
        st[si] = constructSTRecursion(st, arr, ss, mid, left) + constructSTRecursion(st, arr, mid + 1, se, right);
    }

    return st[si];
}

int* constructST(int* arr, int n)
{
    if (!arr || n == 0) {
        return 0;
    }
    // height of segment tree. Use Geometric progression sum formula
    int height = int(ceil(log2(n + 1)) - 1);
    //int height = ceil(log2(n));
    // maximum size of the segment tree
    int max_size = int(pow(2, height + 1) - 1);
    //printf("height: %d, max_size: %d\n", height, max_size);
    int* st = new int[max_size];
    constructSTRecursion(st, arr, 0, n - 1, 0);
    return st;
}

/* A recursive function to update the nodes which have the given
   index in their range. The following are parameters
    st, si, ss and se are same as getSumUtil()
    idx    --> index of the element to be updated. This index is
             in input array.
   diff --> Value to be added to all nodes which have i in range */
void updateValueRecursion(int* st, int ss, int se, int si, int idx, int diff)
{
    //printf("ss: %d, se: %d\n", ss, se);
    // If the input index is in range of this node, then update
    // the value of the node and its children
    if (ss <= idx && idx <= se) {
        st[si] += diff;
        if (ss < se) {
            int mid = (ss + se) >> 1;
            updateValueRecursion(st, ss, mid, 2 * si + 1, idx, diff);
            updateValueRecursion(st, mid + 1, se, 2 * si + 2, idx, diff);
        }
    }
}

void updateValue(int* arr, int* st, int n, int idx, int value)
{
    // the diff of segment sum
    int diff = value - arr[idx];
    updateValueRecursion(st, 0, n - 1, 0, idx, diff);
}

/*  A recursive function to get the sum of values in given range
    of the array. The following are parameters for this function.

    st    --> Pointer to segment tree
    si    --> Index of current node in the segment tree. Initially
              0 is passed as root is always at index 0
    ss & se  --> Starting and ending indexes of the segment represented
                 by current node, i.e., st[si]
    qs & qe  --> Starting and ending indexes of query range */
int getSumRecursion(int* st, int ss, int se, int qs, int qe, int si)
{
    //printf("ss: %d, se: %d, qs: %d, qe: %d, si: %d, st[si]: %d\n",
    //ss, se, qs, qe, si, st[si]);
    if (qs <= ss && se <= qe) {
        // the query range is part of the given range, then return
        // the sum of the segment
        return st[si];
    } else if (qe < ss || se < qs) {
        // query range is outside the given nodes' range
        return 0;
    } else {
        // the segment overlaps with the given range
        int mid = (ss + se) >> 1;
        int left = 2 * si + 1;
        int right = left + 1;
        return getSumRecursion(st, ss, mid, qs, qe, left) + getSumRecursion(st, mid + 1, se, qs, qe, right);
    }
}

// Return sum of elements in range from index qs (quey start)
// to qe (query end).  It mainly uses getSumRecursion()
int getSum(int* st, int n, int qs, int qe)
{
    int ss = 0, se = n - 1;
    int si = 0;
    if (qs < 0 || qs > qe || !st || n <= 0) {
        return 0;
    }
    return getSumRecursion(st, ss, se, qs, qe, si);
}

// Driver program to test above functions
int main()
{
    int arr[] = { 1, 3, 5, 7, 9, 11 };
    int n = sizeof(arr) / sizeof(arr[0]);

    // Build segment tree from given array
    int* st = constructST(arr, n);

    // Print sum of values in array from index 1 to 3
    printf("Sum of values in given range = %d\n",
        getSum(st, n, 1, 3));

    // Update: set arr[1] = 10 and update corresponding
    // segment tree nodes
    updateValue(arr, st, n, 1, 10);

    // Find sum after the value is updated
    printf("Updated sum of values in given range = %d\n",
        getSum(st, n, 1, 3));
    return 0;
}
