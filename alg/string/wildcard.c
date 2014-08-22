/*String matching where one string contains wildcard
characters


Given two strings where first string may contain wild card
characters and second string is a normal string. Write a
function that returns true if the two strings match. The
following are allowed wild card characters in first string.

    * --> Matches with 0 or more instances of any character or set
of characters.
    ? --> Matches with any one character.
For example, "g*ks" matches with "geeks" match. And string
"ge?ks*" matches with "geeksforgeeks" (note '*' at the end of
first string). But "g*k" doesn't match with "gee" as character
'k' is not present in second string.*/

// A C program to match wild card characters
#include <stdio.h>
#include <stdbool.h>

// The main function that checks if two given strings match. The first
// string may contain wildcard characters
// The RECURSION solution passes the small data test,but fails large data ones.
bool match_recursion(char *first, char *second)
{
    // If we reach at the end of both strings, we are done
    if (*first == '\0' && *second == '\0')
        return true;

    // Make sure that the characters after '*' are present in second string.
    // This function assumes that the first string will not contain two
    // consecutive '*'
    if (*first == '*' && *(first + 1) != '\0' && *second == '\0')
        return false;

    // If the first string contains '?', or current characters of both
    // strings match
    if (*first == '?' || *first == *second)
        return match_recursion(first + 1, second + 1);

    // If there is *, then there are two possibilities
    // a) We consider current character of second string
    // b) We ignore current character of second string.
    if (*first == '*')
        return match_recursion(first + 1, second) ||
               match_recursion(first, second + 1);
    return false;
}

// Iteration and backtrack solution.
// The recursion algorithm will do, but will cause TLE.
// Change recursion algorithm to iteration version.
// The algorithm technique is backtrack.
bool wc_match_iteration(char *pattern, char *text)
{
    char *p = pattern, *t = text;
    char *pp = NULL, *tp = NULL; // previous p and t for backtrack.
    while (*t)
    {
        /*if (*p == '\0' && *t == '\0')*/
        /*return true;*/
        if (*p == *t || *p == '?')
        {
            p++;
            t++;
        }
        else if (*p == '*')
        {
            pp = p;
            tp = t;
            p++;
        }
        else
        {
            if (pp && tp)
            {
                tp++;
                p = pp + 1;
                t = tp;
            }
            else
                return false;
        }
    }
    while (*p == '*')
        p++;
    return !*p;
}

// dynamic programming solution.
// Improved algorithm based on the recursion algorithm.
bool wc_match_dp(char *pattern, char *text)
{
    return true;
}

// A function to run test cases
void test_recursion(char *first, char *second)
{
    match_recursion(first, second) ? puts("Yes") : puts("No");
}

void test_iteration(char *pattern, char *text)
{
    wc_match_iteration(pattern, text) ? puts("true") : puts("false");
}

void test_dp(char *pattern, char *text)
{
    wc_match_dp(pattern, text) ? puts("true") : puts("false");
}

void test(char *pattern, char *text)
{
    /*test_recursion(pattern, text);*/
    test_iteration(pattern, text);
}

// Driver program to test above functions
int main()
{
    test("g*ks", "geeks");           // Yes
    test("ge?ks*", "geeksforgeeks"); // Yes
    test("g*k", "gee");              // No because 'k' is not in second
    test("*pqrs", "pqrst");          // No because 't' is not in first
    test("abc*bcd", "abcdhghgbcd");  // Yes
    test("abc*c?d", "abcd"); // No because second must have 2 instances of 'c'
    test("*c*d", "abcd");    // Yes
    test("*?c*d", "abcd");   // Yes
    test("a", "aa");         // Yes
    return 0;
}
