\* dynamic programming, illustrated with Fibonacci sequence as example


----------------------------- MODULE Fibonacci -----------------------------

EXTENDS Integers, Sequences

CONSTANTS
    N

VARIABLES
    f, \* dynamic programming state table 
    i  \* index

vars == << f, i >>

Init == /\ f =  [x \in 1..N |-> IF x = 1 THEN 1 ELSE (IF x = 2 THEN 1 ELSE -1) ]
        /\ i = 3

Transition ==   /\ i < N + 1
                /\ f' = [ f EXCEPT ![i] = f[i-2] + f[i-1] ]
                /\ i' = i + 1

Next == \/ Transition    

Spec == Init /\ [][Next]_<<f , i>>

--------------

Maintenance ==  \/ i < N + 1  
                \/ f[N] = -1

-------------
ActionProperties == /\ [][Transition => f'[i'] = -1 ]_<<vars>>
                    /\ [][f'[i] # -1 ]_<<vars>>

=============================================================================
\* Modification History
\* Last modified Mon Apr 10 18:09:31 CST 2023 by haodu
\* Created Sun Apr 09 11:47:37 CST 2023 by haodu
