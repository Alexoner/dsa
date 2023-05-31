\* BUG: https://bugs.python.org/issue27585
\* reference: https://github.com/Alexander-N/tla-specs/tree/main/asyncio-lock
\*
-------------------------- MODULE asyncioLock27585 --------------------------

EXTENDS Integers, Sequences, asyncioLock

--------------------

\*INSTANCE asyncioLock

------------------------------------------------

BugCancel(t) ==    \* /\ tasks[t].state # CANCELLED
                /\ tasks[t].state = WAITING   \* reproduce original bug: waiting tasks cancelled
                /\ tasks' = [ tasks EXCEPT ![t].state = CANCELLED ]
                /\ UNCHANGED << lock, waitQ >>

--------------------

BugNext == \E t \in Tasks:
                \/ Acquire(t)
                \/ Release(t)
                \/ BugCancel(t)
                \/ Resume(t)
                \/ Terminating  \* avoid deadlock when terminated    

BugSpec == Init    
                /\ [][BugNext]_vars    \* need to specify faireness to rule out stuttering out of interest
\*                /\ \A t \in Tasks: WF_vars(Release(t))

----------------------------------------------------------------------

=============================================================================
\* Modification History
\* Last modified Sun Apr 16 09:58:40 CST 2023 by haodu
\* Created Sun Apr 09 17:48:22 CST 2023 by haodu
