# Representation of Segment trees
1. Leaf Nodes are the elements of the input array.
2. Each internal node represents some merging of the leaf nodes. The merging may be different for different problems. For this problem, merging is sum of leaves under a node.

Just like heap data structure, it is a FULL BINARY TREE(in which every node other than the 
leaves has two children). We can use array to represent a Segment Tree, because the position 
relation between a node and its children's is deterministic.

An ARRAY REPRESENTATION of tree is used to represent Segment Trees. Recursive relation between 
parent and child indexes must be maintained. 
For each node at index i, the left child is at index 2*i+1, right child at 2*i+2 and the parent is
at floor((i-1) / 2).


A Full Binary Tree with n leaves has n-1 internal nodes.
Proof:
    - 1. Mathematical induction
    - in a directed graph, all nodes' in-degree sum is equal to out-degree sum.

    Say the full binary tree has x internal nodes, then the tree's indegree sum is x + n - 1, with
outdegree sum as 2x. Then x = n - 1.

# Construction of segment tree (recursion)
We start with a segment arr[0 . . . n-1]. and every time we divide the current segment into two 
halves(if it has not yet become a segment of length 1), and then call the same procedure on both 
halves, and for each such segment we store the sum in corresponding node.

# Time Complexity:
Time Complexity for tree construction is O(n). There are total 2n-1 nodes, and value of every node
is calculated only once in tree construction.

Time complexity to query is O(Logn). To query a sum, we process at most four nodes at every level
and number of levels is O(Logn).

The time complexity of update is also O(Logn). To update a leaf value, we process one node at
every level and number of levels is O(Logn).
