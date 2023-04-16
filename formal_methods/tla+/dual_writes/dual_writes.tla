\* Reference: https://github.com/Alexander-N/tla-specs/tree/main/dual-writes
\* Problem description: https://martin.kleppmann.com/2015/05/27/logs-for-data-infrastructure.html


---------------------------- MODULE dual_writes ----------------------------

EXTENDS Integers, Sequences, Functions

CONSTANTS 
    NumThreads,  \* integer
    Storage      \* storage set,

Threads == 1..NumThreads

(* --algorithm dual_writes

variables
    values = [ x \in Storage |-> 0 ];
    
define
AllValuesEqual ==
    \A s1, s2 \in Storage: values[s1] = values[s2]
EventualConsistent == <>[]AllValuesEqual
end define

fair process client \in Threads
variables 
        writtenSet = {},
        s = 0;

begin
    Write:
        while writtenSet # Storage do
            s := CHOOSE x \in (Storage \ writtenSet): TRUE;
            writtenSet := writtenSet \cup {s};
            values[s] := self;
        end while
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "c9952f10" /\ chksum(tla) = "9baf5338")
VARIABLES values, pc

(* define statement *)
AllValuesEqual ==
    \A s1, s2 \in Storage: values[s1] = values[s2]
EventualConsistent == <>[]AllValuesEqual

VARIABLES writtenSet, s

vars == << values, pc, writtenSet, s >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ values = [ x \in Storage |-> 0 ]
        (* Process client *)
        /\ writtenSet = [self \in Threads |-> {}]
        /\ s = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "Write"]

Write(self) == /\ pc[self] = "Write"
               /\ IF writtenSet[self] # Storage
                     THEN /\ s' = [s EXCEPT ![self] = CHOOSE x \in (Storage \ writtenSet[self]): TRUE]
                          /\ writtenSet' = [writtenSet EXCEPT ![self] = writtenSet[self] \cup {s'[self]}]
                          /\ values' = [values EXCEPT ![s'[self]] = self]
                          /\ pc' = [pc EXCEPT ![self] = "Write"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << values, writtenSet, s >>

client(self) == Write(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
    
----------------------


=============================================================================
\* Modification History
\* Last modified Wed Apr 12 10:56:36 CST 2023 by haodu
\* Created Tue Apr 11 11:23:57 CST 2023 by haodu
