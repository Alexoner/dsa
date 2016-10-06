# Range Minimum Query

Range Minimum Query (Square Root Decomposition and Sparse Table)
We have an array arr[0 . . . n-1]. We should be able to efficiently find the minimum value from index L (query start) to R (query end) where $0 <= L <= R <= n-1$. Consider a situation when there are many range queries.

Example:

Input:  arr[]   = {7, 2, 3, 0, 5, 10, 3, 12, 18};
        query[] = [0, 4], [4, 7], [7, 8]

Output: Minimum of [0, 4] is 0
        Minimum of [4, 7] is 3
        Minimum of [7, 8] is 12
A simple solution is to run a loop from L to R and find minimum element in given range. This solution takes O(n) time to query in worst case.

Another approach is to use Segment tree. With segment tree, preprocessing time is $O(n)$ and time to for range minimum query is $O(Logn)$. The extra space required is O(n) to store the segment tree. Segment tree allows updates also in $O(Log n)$ time.

# Method 1 (Simple Solution)
A Simple Solution is to create a 2D array $lookup[][]$ where an entry $lookup[i][j]$ stores the minimum value in range $arr[i..j]$. Minimum of a given range can now be calculated in O(1) time.

# Method 2 (Square Root Decomposition)
We can use Square Root Decompositions to reduce space required in above method.

Preprocessing:
1) Divide the range [0, n-1] into different blocks of √n each.
2) Compute minimum of every block of size √n and store the results.

Preprocessing takes $O(√n * √n) = O(n)$ time and $O(√n)$ space.

Query:
1) To query a range [L, R], we take minimum of all blocks that lie in this range. For left and right corner blocks which may partially overlap with given range, we linearly scan them to find minimum.
Time complexity of query is O(√n). Note that we have minimum of middle block directly accessible and there can be at most O(√n) middle blocks. There can be atmost two corner blocks that we may have to scan, so we may have to scan 2*O(√n) elements of corner blocks. Therefore, overall time complexity is O(√n).

# Method 3 (Sparse Table Algorithm)
The above solution requires only O(√n) space, but takes O(√n) time to query. Sparse table method supports query time O(1) with extra space O(n Log n).

The idea is to precompute minimum of all subarrays of size $2^j$ where $j$ varies from 0 to $log n$. Like method 1, we make a lookup table. Here $lookup[i][j]$ contains minimum of range starting from $i$ and of size $2^j$. For example $lookup[0][3]$ contains minimum of range [0, 7] (starting with 0 and of size $2^3=8$)

Preprocessing:
How to fill this lookup table? The idea is simple, fill in bottom up manner using previously computed values.

For example, to find minimum of range [0, 7], we can use minimum of following two.
a) Minimum of range [0, 3]
b) Minimum of range [4, 7]
Since we do only one comparison, time complexity of query is O(1).
Core idea: binarily divide the query range into two parts. And the two parts must overlap with each other.
Preprocessing can be done with dynamic programming procedure.
