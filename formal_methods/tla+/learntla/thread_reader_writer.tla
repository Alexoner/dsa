---- MODULE reader_writer ----
EXTENDS Integers, Sequences, TLC

(* --algorithm reader_writer
variables
  queue = <<>>;
  total = 0;


process writer = 1
begin
  AddToQueue:
    queue := Append(queue, 1);
end process;

process reader = 0
begin
  ReadFromQueue:
\*    if queue # <<>> then   \* interpreted as branch
        await queue # <<>>;  \* translated as enabling condition for action
        total := total + Head(queue);
        queue := Tail(queue);
\*    end if;     
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a0140c9a" /\ chksum(tla) = "88aff5d7")
VARIABLES queue, total, pc

vars == << queue, total, pc >>

ProcSet == {1} \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "AddToQueue"
                                        [] self = 0 -> "ReadFromQueue"]

AddToQueue == /\ pc[1] = "AddToQueue"
              /\ queue' = Append(queue, 1)
              /\ pc' = [pc EXCEPT ![1] = "Done"]
              /\ total' = total

writer == AddToQueue

ReadFromQueue == /\ pc[0] = "ReadFromQueue"
                 /\ queue # <<>>
                 /\ total' = total + Head(queue)
                 /\ queue' = Tail(queue)
                 /\ pc' = [pc EXCEPT ![0] = "Done"]

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer \/ reader
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====


=============================================================================
\* Modification History
\* Last modified Tue Apr 04 18:36:08 CST 2023 by haodu
\* Created Tue Apr 04 17:00:19 CST 2023 by haodu
