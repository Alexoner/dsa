\* https://leetcode.com/problems/n-queens/
\* solve this with dfs, places queens row by row
\* this module finds only one solution
\* TODO: how to find all solutions without exhausting the state space?
\* TODO: how to count states satisfying a certain condition?

------------------------------ MODULE NQueens ------------------------------
EXTENDS Integers, Sequences 

CONSTANTS
    N
    
VARIABLES
    rows, 
    idx

vars == << rows, idx >>    
  

Init == /\ rows = [ x \in 1..N |-> 0 ]
        /\ idx = 1

TypeOK == rows \in [ 1..N -> 0..N ]

-----------------------------------------------

\* functions
Abs(x) == IF x < 0 THEN -x ELSE x    
    
CanAttack(i, j, v) ==   \/ rows[i] = v
                        \/ Abs(rows[i] - v) = Abs(i - j)     \* slope is 1, -1
\*                        \/ Abs(rows[i] - v) = N - Abs(i - j) \* slope is -1

Place(j) == \E v \in 1..N: 
                /\ \A i \in 1..(j-1):
                    /\ ~CanAttack(i, j, v)
                /\ rows' = [ rows EXCEPT ![j] = v ]
                /\ idx' = idx + 1

\* need to disable deadlock check if not specifying looping state transition
Next == \/ Place(idx)
\*        \/ 

Spec == Init /\ [][Next]_vars

Invariant == idx # N + 1

=============================================================================
\* Modification History
\* Last modified Sat Apr 08 18:29:57 CST 2023 by haodu
\* Created Sat Apr 08 17:28:10 CST 2023 by haodu
