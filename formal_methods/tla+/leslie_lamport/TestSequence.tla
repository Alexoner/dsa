---------------------------- MODULE TestSequence ----------------------------

EXTENDS Integers, Sequences

Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> 
                    IF j < i THEN seq[j] 
                    ELSE seq[j + 1] 
                  ]

Rm == Remove(3, <<1,2,3,4>>)
Cartesian == (1..3) \X {"a", "b"}

Init == 1
Next == UNCHANGED <<Rm, Cartesian>>

=============================================================================
\* Modification History
\* Last modified Sun Apr 02 19:51:29 CST 2023 by haodu
\* Created Sun Apr 02 19:36:11 CST 2023 by haodu
