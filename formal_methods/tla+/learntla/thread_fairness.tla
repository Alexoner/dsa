\* strong fairness vs weak fairness and liveness 

---- MODULE thread_fairness ----
EXTENDS Integers
CONSTANT NULL

Threads == 1..2

(*--algorithm threads
variable lock = NULL;

define
  Liveness == 
    \A t \in Threads:
      <>(lock = t)  \* FIXME: liveness property doesn't hold in weak fairness spec.  
end define;

fair process thread \in Threads
begin
  GetLock:
    await lock = NULL;
    lock := self;
  ReleaseLock:
    lock := NULL;
  Reset:
    goto GetLock;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b1f06ff" /\ chksum(tla) = "cebb2d29")
VARIABLES lock, pc

(* define statement *)
Liveness ==
  \A t \in Threads:
    <>(lock = t)


vars == << lock, pc >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ lock = NULL
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ lock = NULL
                 /\ lock' = self
                 /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ lock' = NULL
                     /\ pc' = [pc EXCEPT ![self] = "Reset"]

Reset(self) == /\ pc[self] = "Reset"
               /\ pc' = [pc EXCEPT ![self] = "GetLock"]
               /\ lock' = lock

thread(self) == GetLock(self) \/ ReleaseLock(self) \/ Reset(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====


=============================================================================
\* Modification History
\* Last modified Wed Apr 05 09:43:13 CST 2023 by haodu
\* Created Tue Apr 04 19:56:37 CST 2023 by haodu
