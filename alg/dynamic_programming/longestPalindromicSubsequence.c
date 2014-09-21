/*
 * Dynamic Programming | Longest Palindromic Subsequence
 *
 * Given a sequence, find the length of the longest palindromic subsequence
 * in it. For example, if the given sequence is “BBABCBCAB”, then the
 * output should be 7 as "BABCBAB" is the longest palindromic subseuqnce in
 * it. "BBBBB" and "BBCBB" are also palindromic subsequences of the given
 * sequence, but not the longest ones.
 *
 * Algorithm:
 * Dynamic Programming.
 * Method 1:
 * Maintain a table[i][j] to indicate the length of palindromic subsequence
 * of string[i...j].
 *
 * Method 2:
 * Reverse the string,find the longest common subsequence.
 *
 */
