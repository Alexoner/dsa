/*
 * http://www.geeksforgeeks.org/searching-for-patterns-set-5-finite-automata/
 *
 * Searching for Patterns
 *
 * Finite Automata(FA) based pattern searching algorithm.
 *
 * In Finite State Machine based algorithm, we preprocess the pattern and build
 * a 2D array that represents a Finite Automata. CONSTRUCTION of the FA is the
 * main tricky part of this algorithm. Once the FA is built, the searching is
 * simple. In search, we simply need to start from the first state of the
 * automata and first character of the text. At every step, we consider
 * next character of text, look for the NEXT STATE in the built FA and
 * move to new state. If we reach FINAL STATE, then pattern is found in
 * text. Time complexity of the search prcess is O(n).
 *
 * Before we discuss FA construction, let us take a look at the following FA
 * for pattern ACACAGA.
 * (graph: finiteAutomataFA11.png,finiteAutomataFA2.png)
 *
 * Number of states in FA will be M+1 where M is length of the pattern. The
 * main thing to construct FA is to get the next state from the current
 * state for every possible character. Given a character x and a state k,we
 * can get the next state by considering the string “pat[0..k-1]x” which is
 * basically concatenation of pattern characters pat[0], pat[1] … pat[k-1]
 * and the character x. The idea is to get length of the longest prefix of
 * the given pattern such that the prefix is also suffix of “pat[0..k-1]x”.
 * The value of length gives us the next state. For example, let us see how
 * to get the next state from current state 5 and character ‘C’ in the above
 * diagram. We need to consider the string, “pat[0..5]C” which is “ACACAC”.
 * The length of the longest prefix of the pattern such that the prefix is
 * suffix of “ACACAC”is 4 (“ACAC”). So the next state (from state 5) is 4
 * for character ‘C’.
 *
 * In the following code, computeTF() constructs the FA. The time complexity
 * of the computeTF() is O(m^3*NO_OF_CHARS) where m is length of the pattern
 * and NO_OF_CHARS is size of alphabet (total number of possible characters
 * in pattern and text). The implementation tries all possible prefixes
 * starting from the longest possible that can be a suffix of “pat[0..k-1]x”
 * . There are better implementations to construct FA in O(m*NO_OF_CHARS)
 * (Hint: we can use something like lps array construction in KMP algorithm)
 * .
 */

#include<stdio.h>
#include<string.h>
#define NO_OF_CHARS 256

int getNextState(char *pat, int M, int state, int x)
{
    // If the character c is same as next character in pattern,
    // then simply increment state
    if (state < M && x == pat[state])
        return state + 1;

    int ns, i;  // ns stores the result which is next state

    // ns finally contains the longest prefix which is also suffix
    // in "pat[0..state-1]c"

    // Start from the largest possible value and stop when you find
    // a prefix which is also suffix
    for (ns = state; ns > 0; ns--)
    {
        if (pat[ns - 1] == x)
        {
            for (i = 0; i < ns - 1; i++)
            {
                if (pat[i] != pat[state - ns + 1 + i])
                    break;
            }
            if (i == ns - 1)
                return ns;
        }
    }

    return 0;
}

/* This function builds the TF table which represents Finite Automata for a
   given pattern  */
void computeTF(char *pat, int M, int TF[][NO_OF_CHARS])
{
    int state, x;
    for (state = 0; state <= M; ++state)
        for (x = 0; x < NO_OF_CHARS; ++x)
            TF[state][x] = getNextState(pat, M,  state, x);
}

/* Prints all occurrences of pat in txt */
void search(char *pat, char *txt)
{
    int M = strlen(pat);
    int N = strlen(txt);

    int TF[M + 1][NO_OF_CHARS];

    computeTF(pat, M, TF);

    // Process txt over FA.
    int i, state = 0;
    for (i = 0; i < N; i++)
    {
        state = TF[state][txt[i]];
        if (state == M)
        {
            printf ("\n pattern found at index %d", i - M + 1);
        }
    }
}

// Driver program to test above function
int main()
{
    char *txt = "AABAACAADAABAAABAA";
    char *pat = "AABA";
    search(pat, txt);
    return 0;
}

/*
 * References:
 * Introduction to Algorithms by Thomas H. Cormen, Charles E. Leiserson,
 * Ronald L. Rivest, Clifford Stein
 */

