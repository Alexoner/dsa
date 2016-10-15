/*
 * Searching for Patterns | KMP algorithm
 *
 * KMP algorithm is a Finite Automata based algorithm, with optimization on
 * computing STATE TRANSITION function with Prefix Function. The preprocessing
 * construct an auxiliary array lps[](lps indicates LONGEST proper PREFIX which
 * is also SUFFIX).
 * lps[i] indicates the length of lps of substring patten[0...i].
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void computeLPSArray(char *pat, int m, int *lps)
{
    lps[0] = 0;
    int q = 0; // number of matched characters

    // scan the pattern from left to right
    for (int i = 1; i < m; ++i) {
        while(q && pat[i] != pat[q]) {
            q = lps[q - 1];
        }

        if (pat[q + 1] == pat[i]) {
            q += 1;
        }
        lps[i] = q;
    }
}

int KMPSearch(char *pat, char *txt)
{
    int n = strlen(txt);
    int m = strlen(pat);
    int q = 0; // number of characters matched
    int lps[m];
    computeLPSArray(pat, m, lps);

    // scan text from left to right
    for (int i = 0; i < n; ++i)
    {
        while(q && pat[q] != txt[i]) {
            q = lps[q - 1]; // next character does not match
        }
        if (pat[q] == txt[i]) {
            q += 1; // next character matches
        }

        if (q == m) {
            printf("Pattern occurs with shift %d\n", i - m + 1);
            q = lps[q - 1]; // looking for next match?
            /*return i;*/
        }
    }
    return 0;
}


// Driver program to test KMP algorithm
int main()
{
    char *txt = "ABABDABACDABABCABABCBABABCABAB";
    char *pat = "ABABCABAB";
    KMPSearch(pat, txt);

    return 0;
}
