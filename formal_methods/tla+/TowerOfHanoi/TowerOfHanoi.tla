(* https://en.wikipedia.org/wiki/Tower_of_Hanoi *)
(***************************************************************************)
(* A disk can be moved if:                                                 *)
(*  - The source position is different from the destination.               *)
(*  - The source tower is not empty.                                       *)
(*  - The top disk of the source tower is smaller than the top disk of     *)
(*    the destination tower.                                               *)
(***************************************************************************)
\* solution is found by breaking the invariant of no solution yet.

----------------------------- MODULE TowerOfHanoi -----------------------------

EXTENDS Integers, Sequences, Functions

CONSTANTS
    N,  \* n disks
    M   \* m plates
    
VARIABLES
    plates
    

vars == << plates >>

typeOK == /\ \A sequence \in Range(plates): sequence \in [ 1..Len(sequence) -> 1..N ]

----------------------------------------------------------------------------------------    
Init == /\ plates = [ x \in 1..M |-> IF x = 1 THEN [ y \in 1..N |-> y]  ELSE <<>> ]

Move(f, t) ==   /\ f # t
                /\ Len(plates[f]) # 0
                /\  LET top == IF Len(plates[t]) = 0 THEN N + 1 ELSE Head(plates[t])
                    IN Head(plates[f]) < top 
                /\ plates' = [plates EXCEPT ![f] = Tail(plates[f]),
                                            ![t] = <<Head(plates[f])>> \o plates[t]
                             ]

Next == /\ \E f, t \in 1..M: Move(f, t)

Spec == Init /\ [][Next]_vars

Invariant == Len(plates[M]) # N

=============================================================================
\* Modification History
\* Last modified Sat Apr 08 17:26:30 CST 2023 by haodu
\* Created Sat Apr 08 15:09:15 CST 2023 by haodu
