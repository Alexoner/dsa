\* Original snapshot: https://github.com/aio-libs/aiorwlock/blob/b00c1090f2bb737873ae6f4b480c7e5740ffa3c3/aiorwlock/__init__.py
\* BUG: https://github.com/aio-libs/aiorwlock/pull/37
\* FIX PR: https://github.com/aio-libs/aiorwlock/pull/39/files
\* This specification reproduces the bug.
\* Note: this doesn't specify all behaviours of the implementation: minimal spec w.r.t State.
\*  - no wait for future, no notification for fairness of threads
\*  - self._owning abstracted as Lock state {"waiting", "Read", "WriteRead"}

----------------------------- MODULE aiorwlock_bug ------------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets
CONSTANTS Task
ASSUME /\ Task # {}

VARIABLES State,
          Lock

-----------------------------------------------------------------------------
TypeOK == /\ Lock \in [Task -> {"Read", "Write", "WriteRead", "Waiting", "Finished"}]
          /\ State >= -2
LockInit == Lock = [t \in Task |-> "Waiting"] /\ State = 0
-----------------------------------------------------------------------------


Rlocked == State > 0
Wlocked == State < 0
Unlocked == ~Rlocked /\ ~Wlocked

WOwn(t) == Lock[t] \in {"Write"}

RAquire(t) == \/ /\ ~Wlocked
                 /\ Lock[t] \in {"Waiting"}
                 /\ Lock' = [Lock EXCEPT ![t] = "Read"]
                 /\ State' = State + 1
              \/ /\ WOwn(t)
                 /\ Lock' = [Lock EXCEPT ![t] = "WriteRead"]
                 /\ State' = State + 1

WAquire(t) == /\ Unlocked
              /\ Lock[t] \in {"Waiting"}
              /\ Lock' = [Lock EXCEPT ![t] = "Write"]
              /\ State' = State - 1

RRelease(t) == \/ /\ Rlocked /\ Lock[t] = "Read"
                  /\ State' = State - 1 /\ Lock' = [Lock EXCEPT ![t] = "Finished"]
               \/ /\ Rlocked /\ Lock[t] = "WriteRead"
                  /\ State' = State - 1 /\ Lock' = [Lock EXCEPT ![t] = "Write"]

WRelease(t) == \/ /\ Wlocked /\ Lock[t] = "Write"
                  /\ State' = State + 1 /\ Lock' = [Lock EXCEPT ![t] = "Finished"]
               \/ /\ Wlocked /\ Lock[t] = "WriteRead"
                  /\ State' = State + 1 /\ Lock' = [Lock EXCEPT ![t] = "Read"]

-----------------------------------------------------------------------------
vars == <<State, Lock>>

Terminating ==  /\ \A t \in Task:   /\ Lock[t] = "Finished"
                /\ UNCHANGED vars

-----------------------------------------------------------------------------

Next == \/ \E t \in Task:  \/ RAquire(t) \/ WAquire(t) \/ RRelease(t) \/ WRelease(t)
        \/ Terminating

Spec == LockInit /\ [][Next]_vars


\* LockInv ==
\*     \A t1 \in Task : \A t2 \in (Task \ {t1}): ~
\*         (/\ Lock[t1] \in {"Write", "WriteRead"}
\*          /\ Lock[t2] \in {"Read", "Write", "WriteRead"})

Exclusive == \A t \in Task: Lock[t] \notin {"Waiting", "Finished"} => State # 0

LockInv ==
    \A t1 \in Task : \A t2 \in (Task \ {t1}):
      Lock[t1] \in {"Write", "WriteRead"} => Lock[t2] \in {"Waiting", "Finished"}

-----------------------------------------------------------------------------

THEOREM Spec => [](TypeOK /\ LockInv /\ Exclusive)

=============================================================================