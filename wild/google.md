1. String Decompression，把"a2b3c4"->"aabbbcccc"
    Follow Up: 输入是个Iterator，输出也是Iterator
2. a. 给一个int array，找一个数，左边的和与右边的和相等，O(n)
    b. n/4 Popular Element，找Quartile，用binary search.
3. LC399，dfs
4. 给一个String，问到"a*b*"的edit distance，O(n^2) -> O(n)/O(n) -> O(n)/O(1)，计数就行了
    Follow Up: "a*b*c*"，要求O(n)/O(1)，提示之下用了DP


 5. 
一共五轮面试，四轮coding加一轮PhD。
coding 1：编码解码。比如A是1，B是2。。。Z是26，第一问是一串字母（e.g.,ABACCC），编码成数字
    第二问是给定一串数字（e.g.,123121452），解码成所有可能的字符串，follow up是怎么改进performance
coding 2：matrix sum/update，是leetcode 原题，好像是308         Range Sum Query 2D - Mutable.

coding 3：给定matrix数字，找出最长的increase path

coding 4：给定一个string，写两个函数addString，delString，
    e.g., addString(int offset, String srcStr, String destStr)，是在destStr中的offset加入新的srcStr，返回String。delString(String Str, int offset, int length)就是在Str中offset的位置删除长度为length的str，自己设计数据结构.


Given a binary tree, find the path which nodes sum to a given value. The path can start from and end with any nodes
