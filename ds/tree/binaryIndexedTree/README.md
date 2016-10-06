# Binary Indexed Tree or Fenwick Tree
Let us consider the following problem to understand Binary Indexed Tree.

We have an array $arr[0 . . . n-1]$. We should be able to
1 Find the sum of first i elements.
2 Change value of a specified element of the array arr[i] = x where $0 <= i <= n-1$.

A simple solution is to run a loop from 0 to i-1 and calculate sum of elements. To update a value, simply do arr[i] = x. The first operation takes O(n) time and second operation takes O(1) time. Another simple solution is to create another array and store sum from start to i at the i’th index in this array. Sum of a given range can now be calculated in O(1) time, but update operation takes O(n) time now. This works well if the number of query operations are large and very few updates.

## Can we perform both the operations in O(log n) time once given the array? 
One Efficient Solution is to use Segment Tree that does both operations in $O(Logn)$ time.

Using Binary Indexed Tree, we can do both tasks in $O(Logn)$ time. The advantages of Binary Indexed Tree over Segment are, requires less space and very easy to implement..

## Representation
Binary Indexed Tree is represented as an array. Let the array be BITree[]. Each node of Binary Indexed Tree stores sum of some elements of given array. Size of Binary Indexed Tree is equal to n where n is size of input array. In the below code, we have used size as n+1 for ease of implementation.

## Construction
We construct the Binary Indexed Tree by first initializing all values in BITree[] as 0. Then we call update() operation for all indexes to store actual sums, update is discussed below.

## Operations
```code
getSum(index): Returns sum of arr[0..index]
// Returns sum of arr[0..index] using BITree[0..n].  It assumes that
// BITree[] is constructed for given array arr[0..n-1]
1) Initialize sum as 0 and index as index+1.
2) Do following while index is greater than 0.
...a) Add BITree[index] to sum
...b) Go to parent of BITree[index].  Parent can be obtained by removing
     the last set bit from index, i.e., index = index - (index & (-index))
3) Return sum.
```
