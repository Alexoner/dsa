\* threads model, combining previous concepts

\*Tips: help action
\*Trans(state, from, to) ==
\*  /\ pc[state] = from
\*  /\ pc' = [pc EXCEPT ![state] = to]
\*
\*IncCounter(self) ==
\*  /\ Trans(self, "IncCounter", "Done")
\*  /\ counter' = counter + 1
  
---- MODULE threads ----
EXTENDS TLC, Sequences, Integers

CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 0;
  lock = NULL;

define

\* action properties
  CounterOnlyIncreases ==
    [][counter' >= counter]_counter  \* action property: counter increases or stay unchanged
    
  LockCantBeStolen ==
    [][lock # NULL => lock' = NULL]_lock     
    
  LockNullBeforeAcqure ==
    [][lock' # NULL => lock = NULL]_lock  
    
\*  CounterOnlyIncreases == 
\*      \A c \in Counters:
\*        [][values[c]' >= values[c]]_values[c]    
         
  AllDone == 
    \A t \in Threads: pc[t] = "Done"

  \* invariants
  Correct ==
      AllDone => counter = NumThreads
end define;  

process thread \in Threads
variables tmp = 0;

begin
  GetLock:
\*    await lock = NULL; \* elsewise breaks action propertyLockCantBeStolen
    lock := self;

  GetCounter:
    tmp := counter;

  IncCounter:
    counter := tmp + 1;
  
  ReleaseLock:
    lock := NULL; 
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "d5b0d0c8" /\ chksum(tla) = "3e15bc7d")
VARIABLES counter, lock, pc

(* define statement *)
CounterOnlyIncreases ==
  [][counter' >= counter]_counter

LockCantBeStolen ==
  [][lock # NULL => lock' = NULL]_lock

LockNullBeforeAcqure ==
  [][lock' # NULL => lock = NULL]_lock





AllDone ==
  \A t \in Threads: pc[t] = "Done"


Correct ==
    AllDone => counter = NumThreads

VARIABLE tmp

vars == << counter, lock, pc, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 0
        /\ lock = NULL
        (* Process thread *)
        /\ tmp = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
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

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

-------------------------------------

FairSpec == /\ Init /\ [][Next]_vars
            /\ \A self \in Threads : SF_vars(thread(self))


=============================================================================
\* Modification History
\* Last modified Wed Apr 12 10:26:18 CST 2023 by haodu
\* Created Mon Apr 03 16:56:13 CST 2023 by haodu
