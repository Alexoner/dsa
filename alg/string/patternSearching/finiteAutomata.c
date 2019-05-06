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
 * can get the next state by considering the string “pattern[0..k-1]x” which is
 * basically concatenation of pattern characters pattern[0], pattern[1] … pattern[k-1]
 * and the character x. The idea is to get length of the longest prefix of
 * the given pattern such that the prefix is also suffix of “pattern[0..k-1]x”.
 * The value of length gives us the next state. For example, let us see how
 * to get the next state from current state 5 and character ‘C’ in the above
 * diagram. We need to consider the string, “pattern[0..5]C” which is “ACACAC”.
 * The length of the longest prefix of the pattern such that the prefix is
 * suffix of “ACACAC”is 4 (“ACAC”). So the next state (from state 5) is 4
 * for character ‘C’.
 *
 * In the following code, computeTransitionFunction() constructs the FA. The time complexity
 * of the computeTransitionFunction() is O(m^3*NO_OF_CHARS) where m is length of the pattern
 * and NO_OF_CHARS is size of alphabet (total number of possible characters
 * in pattern and text). The implementation tries all possible prefixes
 * starting from the longest possible that can be a suffix of “pattern[0..k-1]x”
 * . There are better implementations to construct FA in O(m*NO_OF_CHARS)
 *
 * (Hint: we can use something like LPS array construction in KMP algorithm)
 * .
 *
 * Takeaway
 * =========
 * 1. A brute force search takes O(mn) time complexity. This method is actually tracking
 * state of LENGTH BEGINNING HERE.
 * 2. Keep track of the state as LENGTH ENDING HERE(length of prefix matched so far), and build a
 * finite state machine to search takes O(mk) time to preprocess and O(n) time to search.
 * 3. Build a sparse finite state machine, like in KMP, will reduce the preprocessing
 * time complexity to O(m).
 *
 */

#include <stdio.h>
#include <string.h>
#define NO_OF_CHARS 256

int getNextState(char* pattern, int pattern_len, int state, int ch)
{
    // If the character c is same as next character in pattern,
    // then simply increment state
    if (state < pattern_len && ch == pattern[state])
        return state + 1;

    int ns, i; // ns stores the result which is next state

    // ns finally contains the longest prefix which is also suffix
    // in "pattern[0..state-1]c"

    // Start from the largest possible value and stop when you find
    // a prefix which is also suffix
    // O(m^2) time complexity to compute next state
    for (ns = state; ns > 0; ns--) {
        if (pattern[ns - 1] == ch) {
            for (i = 0; i < ns - 1; i++) {
                if (pattern[i] != pattern[state - ns + 1 + i])
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
void computeTransitionFunction(char* pattern, int pattern_len, int TF[][NO_OF_CHARS])
{
    int state, ch;
    for (state = 0; state <= pattern_len; ++state)
        for (ch = 0; ch < NO_OF_CHARS; ++ch)
            TF[state][ch] = getNextState(pattern, pattern_len, state, ch);
}

/* Prints all occurrences of pattern in txt */
void search(char* pattern, char* txt)
{
    int M = strlen(pattern);
    int N = strlen(txt);

    int TF[M + 1][NO_OF_CHARS];

    computeTransitionFunction(pattern, M, TF);

    // Process txt over FA.
    int i, state = 0;
    for (i = 0; i < N; i++) {
        state = TF[state][txt[i]];
        if (state == M) {
            printf("\n pattern found at index %d", i - M + 1);
        }
    }
}

// Driver program to test above function
int main()
{
    char* txt = "AABAACAADAABAAABAA";
    char* pattern = "AABA";
    search(pattern, txt);
    return 0;
}

/*
 * References:
 * Introduction to Algorithms by Thomas H. Cormen, Charles E. Leiserson,
 * Ronald L. Rivest, Clifford Stein
 */
