\* model concurrent systems, evaluate with invariant & action properties


---- MODULE thread_concurrency ----
EXTENDS TLC, Sequences, Integers

CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
\*  counter = 0;
    counter = 1;  \* FIXME: passes Liveness == <>(counter = NumThreads), but not <>[](counter=NumThreads)
  lock = NULL;

define
  AllDone == 
    \A t \in Threads: pc[t] = "Done"

  Correct ==
      AllDone => counter = NumThreads
      
\*  Liveness == <>(counter = NumThreads)  \* eventual true, could be false afterwards
  Liveness == <>[](counter = NumThreads)  \* eventually always true, stays true
  
end define;  

\*fair: specify weak faireness for the spec
\*fair+: specify strong faireness for the spec
fair+ process thread \in Threads
variables tmp = 0;
begin
  GetLock:
    await lock = NULL;
    lock := self;
       
  GetCounter:
    tmp := counter;

  IncCounter:
    counter := tmp + 1;
    
  ReleaseLock:
    assert lock = self;
    lock := NULL;
    
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d7bad5e5" /\ chksum(tla) = "a389dc18")
VARIABLES counter, lock, pc

(* define statement *)
AllDone ==
  \A t \in Threads: pc[t] = "Done"

Correct ==
    AllDone => counter = NumThreads


Liveness == <>[](counter = NumThreads)

VARIABLE tmp

vars == << counter, lock, pc, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 1
        /\ lock = NULL
        (* Process thread *)
        /\ tmp = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ lock = NULL
                 /\ lock' = self
                 /\ pc' = [pc EXCEPT ![self] = "GetCounter"]
                 /\ UNCHANGED << counter, tmp >>

GetCounter(self) == /\ pc[self] = "GetCounter"
                    /\ tmp' = [tmp EXCEPT ![self] = counter]
                    /\ pc' = [pc EXCEPT ![self] = "IncCounter"]
                    /\ UNCHANGED << counter, lock >>

IncCounter(self) == /\ pc[self] = "IncCounter"
                    /\ counter' = tmp[self] + 1
                    /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
                    /\ UNCHANGED << lock, tmp >>

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ Assert(lock = self, 
                               "Failure of assertion at line 44, column 5.")
                     /\ lock' = NULL
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << counter, tmp >>

thread(self) == GetLock(self) \/ GetCounter(self) \/ IncCounter(self)
                   \/ ReleaseLock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : SF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====


=============================================================================
\* Modification History
\* Last modified Wed Apr 05 09:40:34 CST 2023 by haodu
\* Created Tue Apr 04 13:29:58 CST 2023 by haodu
