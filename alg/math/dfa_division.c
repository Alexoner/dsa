

/*
 * DFA based division
 *
 * Deterministic Finite Automata (DFA) can be used to check whether a
 * number "num" is divisible by "k" or not.If the number is not divisible,
 * the remainder can also be obtained using DFA.
 *We consider the binary representation of ‘num’ and build a DFA with k
 states. The DFA has transition function for both 0 and 1. Once the DFA is
 built, we process ‘num’ over the DFA to get remainder.

Let us walk through an example. Suppose we want to check whether a given
number ‘num’ is divisible by 3 or not. Any number can be written in the
form: num = 3*a + b where ‘a’ is the quotient and ‘b’ is the remainder.
For 3, there can be 3 states in DFA, each corresponding to remainder 0, 1
and 2.
And each state can have two transitions corresponding 0 and 1 (considering
the binary representation of given ‘num’).
The transition function F(p, x) = q tells that on reading alphabet x, we
move from state p to state q. Let us name the states as 0, 1 and 2. The
initial state will always be 0. The final state indicates the remainder. If
the final state is 0, the number is divisible.

In the above diagram, double circled state is final state.

1. When we are at state 0 and read 0, we remain at state 0.
2. When we are at state 0 and read 1, we move to state 1, why? The number so
formed(1) in decimal gives remainder 1.
3. When we are at state 1 and read 0, we move to state 2, why? The number so
formed(10) in decimal gives remainder 2.
4. When we are at state 1 and read 1, we move to state 0, why? The number so
formed(11) in decimal gives remainder 0.
5. When we are at state 2 and read 0, we move to state 1, why? The number so
formed(100) in decimal gives remainder 1.
6. When we are at state 2 and read 1, we remain at state 2, why? The number so
formed(101) in decimal gves remainder 2.

The transition table looks like following:

state   0   1
_____________
 0      0   1
 1      2   0
 2      1   2

Let us check whether 6 is divisible by 3?
Binary representation of 6 is 110
state = 0
1. state=0, we read 1, new state=1
2. state=1, we read 1, new state=0
3. state=0, we read 0, new state=0
Since the final state is 0, the number is divisible by 3.

Let us take another example number as 4
state=0
1. state=0, we read 1, new state=1
2. state=1, we read 0, new state=2
3. state=2, we read 0, new state=1
Since, the final state is not 0, the number is not divisible by 3. The remainder
is 1.

Note that the final state gives the remainder.

We can extend the above solution for any value of k. For a value k, the
states would be 0, 1, …. , k-1. How to calculate the transition if the
decimal equivalent of the binary bits seen so far, crosses the range k? If
we are at state p, we have read p (in decimal). Now we read 0, new read
number becomes 2*p. If we read 1, new read number becomes 2*p+1. The new
state can be obtained by subtracting k from these values (2p or 2p+1) where
0 <= p < k.
*/

#include <stdio.h>
#include <stdlib.h>

// Function to build DFA for divisor k
void preprocess(int k, int table[][2])
{
    int trans0, trans1;
    int state;
    int i;

    // The following loop calculates the two transitions for each stae
    // starting from state 0
    for (state = 0; state < k; state++)
    {
        for (i = 0; i < 2; i++)
        {
            table[state][i] = (state << 1) + i;
            if (table[state][i] >= k)
            {
                table[state][i] -= k;
            }
        }
    }
}

// A recursive utility that takes a 'num' and DFA(transition function
// table) as input and process 'num' bit by bit over DFA
void isDivisibleUtil(int num, int *state, int table[][2])
{
    // process "num" bit by bit from MSB to LSB
    *state = table[0][0];

    if (num)
    {
        isDivisibleUtil(num >> 1, state, table);
        *state = table[*state][num & 1];
    }
    else
    {
        *state = 0;
    }
}

// The main function that provides 'num' by k and returns the remainder
int isDivisible(int num, int k)
{
    // Allocate memory for transition table.The table is
    // of size k*2*sizeof(int)
    int(*table)[2] = (int(*)[2])malloc(k * sizeof(*table));

    preprocess(k, table);

    // process "num" over DFA and get the remainder
    int state = 0;
    isDivisibleUtil(num, &state, table);

    // the final state value is the remainder
    return state;
}

// Driver program
int main(int argc, char **argv)
{
    int num = 47; // dividend
    int k = 5;    // divisor

    int remainder = isDivisible(num, k);

    if (remainder == 0)
        printf("Divisible\n");
    else
        printf("Not divisible,remainder is: %d\n", remainder);

    return 0;
}
