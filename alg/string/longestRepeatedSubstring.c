/*
 * Longest Repeated Substring
 *
 * the longest repeated substring problem is the problem of finding the
 * longest substring of a string that occurs at least twice. This problem
 * can be solved in linear time and space by building a suffix tree for the
 * string, and finding the deepest internal node in the tree. Depth is
 * measured by the number of characters traversed from the root. The string
 * spelled by the edges from the root to such a node is a longest repeated
 * substring. The problem of finding the longest substring with at least k
 * occurrences can be solved by first preprocessing the tree to count the
 * number of leaf descendants for each internal node, and then finding the
 * deepest node with at least k leaf descendants.
 *
 */
