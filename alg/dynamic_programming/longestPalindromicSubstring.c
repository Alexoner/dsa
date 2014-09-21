/*
 * Longest Palindromic Substring
 *
 * Given a string, find the longest substring which is palindrome. For
 * example, if the given string is “forgeeksskeegfor”, the output should be
 * "geeksskeeg".
 *
 * Method 1(Brute Force):
 * Time Complexity:O(n^3)
 * Auxiliary Complexity:O(1)
 *
 * Method 2(Dynamic Programming):
 *  Similar to Longest Palindromic Subsequence Problem.
 * We maintain a boolean table[n][n] that is filled in bottom up manner.
 * The value of table[i][j] is true, if the substring is palindrome,
 * otherwise false. To calculate table[i][j], we first check the value of
 * table[i+1][j-1], if the value is true and str[i] is same as str[j], then
 * we make table[i][j] true. Otherwise, the value of table[i][j] is made
 * false.
 * Time Complexity:O(n^2)
 * Space Complexity:O(n^2)
 *
 * Method 3(scan)
 * Find a or two center character,scan from center to two ends.
 * Time Complexity:O(n^2)
 * Space Complexity:O(1)
 *
 */
