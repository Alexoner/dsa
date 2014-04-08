/*
 * In the longest-common-subsequence problem, we are given two sequences
 * X= <x1,x2,... , xm> and Y=<y1,y2, ... , yn> and wish to find a maximum-
 * length common subsequence of X and Y .
 *
 * In a brute-force approach to solving the LCS problem, we would enumerate all
 * subsequences of X and check each subsequence to see whether it is also a subse-
 * quence of Y , keeping track of the longest subsequence we find.
 *
 * Theorem 15.1 (Optimal substructure of an LCS)
 *
 * Let X=<x1,x2,... , xm> and Y= <y1,y2,..., yn> be sequences,
 * and let Z= < z1 ,z2 , ... , zk> be any LCS of X and Y .
 * 1. If x[m] = y[n], then z[k]= x[m]= y[n]and Z[k] is an LCS of X[m].
 * 2. If x[m] != y[n], then z[k] != x[m]implies that Z is an LCS of X[m-1]
 * and Y[n- 1] .
 * 3. If x[m] != y[n], then z[k] != y[n] implies that Z is an LCS of X and Y[n-1].
 */
