\* use ShiViz to visualize error trace
\* https://github.com/tlaplus/tlaplus/issues/267#issuecomment-481951259
\* NOTE: without vector clock, it doesn't work.


------------------------- MODULE dual_writes_shiviz -------------------------

EXTENDS Integers, Sequences, ShiViz, TLC

CONSTANTS 
    NumThreads,  \* integer
    Storage,      \* storage set,
    NULL

Threads == 1..NumThreads

(* --algorithm dual_writes

variables
    values = [ x \in Storage |-> 0 ];
    event = NULL;
    host = NULL;
    
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
            host := self;
            event := <<self, s>>;
        end while
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "9c9ec988" /\ chksum(tla) = "84d66766")
VARIABLES values, event, host, pc

(* define statement *)
AllValuesEqual ==
    \A s1, s2 \in Storage: values[s1] = values[s2]
EventualConsistent == <>[]AllValuesEqual

VARIABLES writtenSet, s

vars == << values, event, host, pc, writtenSet, s >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ values = [ x \in Storage |-> 0 ]
        /\ event = NULL
        /\ host = NULL
        (* Process client *)
        /\ writtenSet = [self \in Threads |-> {}]
        /\ s = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "Write"]

Write(self) == /\ pc[self] = "Write"
               /\ IF writtenSet[self] # Storage
                     THEN /\ s' = [s EXCEPT ![self] = CHOOSE x \in (Storage \ writtenSet[self]): TRUE]
                          /\ writtenSet' = [writtenSet EXCEPT ![self] = writtenSet[self] \cup {s'[self]}]
                          /\ values' = [values EXCEPT ![s'[self]] = self]
                          /\ host' = self
                          /\ event' = <<self, s'[self]>>
                          /\ pc' = [pc EXCEPT ![self] = "Write"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << values, event, host, writtenSet, s >>

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



LOCAL ToJSONKeyValue(F, d) == ToString(ToString(d)) \o ":" \o ToString(F[d]) 
RECURSIVE ToJSON(_,_)
LOCAL ToJSON(F, D) == LET d == CHOOSE d \in D: TRUE
                IN IF D = DOMAIN F
                   THEN "{" \o ToJSONKeyValue(F, d) \o ToJSON(F, D \ {d})
                   ELSE ", " \o ToJSONKeyValue(F, d) \o IF D \ {d} = {}
                                                        THEN "}" 
                                                        ELSE ToJSON(F, D \ {d})
ToJSONObject(F) == IF DOMAIN F = {} THEN "{}" ELSE ToJSON(F, DOMAIN F)

=============================================================================
\* Modification History
\* Last modified Wed Apr 12 16:29:35 CST 2023 by haodu
\* Created Wed Apr 12 13:16:40 CST 2023 by haodu
