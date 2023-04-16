------------------------ MODULE asyncioLock27585Fix ------------------------

EXTENDS Functions, asyncioLock27585

\*INSTANCE asyncioLock27585

--------------------------------

EmptyOrCancelled(q) ==  \/ q = <<>>
                        \/ \A t \in Range(q): tasks[t].state = CANCELLED 

FixAcquire(t) ==       \* acquire the lock or put to wait
                /\ tasks[t].state = RUNNING
                /\ tasks[t].lock = RELEASED
                /\  \/  /\ lock = 0       \* enabling condition disjunct: lock acquired by someone else
                        /\ EmptyOrCancelled(waitQ)    
                        /\ lock' = t
                        /\ tasks' = [ tasks EXCEPT ![t].lock = ACQUIRED ] 
                        /\ UNCHANGED waitQ
                    \/  /\  \/ lock # 0
                            \/ ~EmptyOrCancelled(waitQ)   \* wait in queued if locked or others waiting
                        /\ Wait(t)


FixNext == \E t \in Tasks:
    \/ FixAcquire(t)
\*    \/ Acquire(t)
    \/ Release(t)
    \/ Resume(t)
    \/ BugCancel(t)
    \/ Terminating

FixSpec == Init    /\ [][FixNext]_vars    \* need to specify faireness to rule out stuttering out of interest
\*                /\ \A t \in Tasks: WF_vars(Release(t))


=============================================================================
\* Modification History
\* Last modified Tue Apr 11 11:22:43 CST 2023 by haodu
\* Created Mon Apr 10 10:43:55 CST 2023 by haodu
