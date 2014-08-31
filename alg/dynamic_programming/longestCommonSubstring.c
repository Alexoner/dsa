

/*
 * Dynamic Programming (Longest Common Substring)
 *
 *
Given two strings ‘X’ and ‘Y’, find the length of the longest common substring.
For example, if the given strings are “GeeksforGeeks” and “GeeksQuiz”, the
output should be 5 as longest common substring is “Geeks”

Let m and n be the lengths of first and second strings respectively.

A simple solution is to one by one consider all substrings of first string and
for every substring check if it is a substring in second string. Keep track of
the maximum length substring. There will be O(m^2) substrings and we can find
whether a string is subsring on another string in O(n) time (See this). So
overall time complexity of this method would be O(n * m2)



Dynamic Programming can be used to find the longest common substring in O(m*n)
time. The idea is to find length of the Longest Common Suffix for all substrings
of both strings and store these lengths in a table.

The longest common suffix has following optimal substructure property
   LCSuff(X, Y, m, n) = LCSuff(X, Y, m-1, n-1) + 1 if X[m-1] = Y[n-1]
                        0  Otherwise (if X[m-1] != Y[n-1])

The maximum length Longest Common Suffix is the longest common substring.
   LCSubStr(X, Y, m, n)  = Max(LCSuff(X, Y, i, j)) where 1 <= i <= m
                                                     and 1 <= j <= n

*/

/*Dynamic Programming solution to find length of the longest common substring*/

#include <stdio.h>
#include <string.h>

#define MAX(a, b) (a) >= (b) ? (a) : (b)

int LCSubstring(char *x, char *y, int m, int n)
{
    // Create a table to store lengths of longest common suffixes of
    // substrings.Note that LCSuff[i][j] contains length of longest common
    // suffix of X[0..i-1] and Y[0..j-1].The first row and column entries
    // are used for simplicity.
    int LCSuff[m + 1][n + 1];
    int length = 0; // To store the length of the longest common substring
    int end = 0;
    int i, j;

    // Bottom-up
    for (i = 0; i <= m; i++)
        for (j = 0; j <= n; j++)
        {
            if (i == 0 || j == 0)
                LCSuff[i][j] = 0;
            else if (x[i - 1] == y[j - 1])
            {
                LCSuff[i][j] = LCSuff[i - 1][j - 1] + 1;
                /*length = MAX(length, LCSuff[i][j]);*/
                if (length < LCSuff[i][j])
                {
                    length = LCSuff[i][j];
                    end = i;
                }
            }
            else
                LCSuff[i][j] = 0;
        }

    char substring[m];
    strncpy(substring, x + end - length, length);
    printf("Longest Common Substring of \"%s\" and \"%s\" \nis: \"%s\"\n", x, y,
           substring);
    return length;
}

// Driver program
int main(int argc, char **argv)
{
    char X[] = "OldSite:GeeksforGeeks.org";
    char Y[] = "NewSite:GeeksQuiz.com";

    int m = strlen(X);
    char n = strlen(Y);

    printf("Length of longest common substring is: %d\n",
           LCSubstring(X, Y, m, n));

    return 00;
}
