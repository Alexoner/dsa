/*
 * Dynamic Programming: Longest Increasing Subsequence
 * The longest Increasing Subsequence (LIS) problem is to find the length
 * of the longest subsequence of a given sequence such that all elements
 * of the subsequence are sorted in increasing order. For example, length
 * of LIS for { 10, 22, 9, 33, 21, 50, 41, 60, 80 } is 6 and LIS is
 * {10, 22, 33, 50, 60, 80}.
 *
 * Optimal Substructure:
 * Let arr[0..n-1] be the input array and L(i) be the length of the LIS
 * till index i such that arr[i] is part of LIS and arr[i] is the last
 * element in LIS, then L(i) can be recursively written as.
 * L(i) = { 1 + Max ( L(j) ) } where j < i and arr[j] < arr[i] and if
 * there is no such j then L(i) = 1
 * To get LIS of a given array, we need to return max(L(i)) where
 * 0 < i < n
 * So the LIS problem has optimal substructure property as the main
 * problem can be solved using solutions to subproblems.
 */
