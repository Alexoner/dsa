\* after fixing https://bugs.python.org/issue27585
\* there is still a follow up bug: https://bugs.python.org/issue27585
\* deadlock when a task is cancelled upon wake up.
\* PR for fix: https://github.com/python/asyncio/pull/467/files

------------------------- MODULE asyncioLock27585_1 -------------------------

EXTENDS Functions, asyncioLock27585Fix

--------------------------------

                            
CancelWhenWakeUp(t) ==    
                /\ tasks[t].state \in { WAITING, RESUME }
                /\ tasks' = [ tasks EXCEPT ![t].state = CANCELLED ]
                /\ UNCHANGED << lock, waitQ >>

NextNonCancelled(t) ==  
    LET waitList == SelectSeq(waitQ, LAMBDA x: tasks[x].state # CANCELLED /\ x # t)
    IN 
        IF waitList = <<>>
        THEN 0
        ELSE Head(waitList)

FixCancel(t) ==    
                /\ tasks[t].state \in { WAITING, RESUME }   \* reproduce original bug: waiting tasks cancelled
                /\  \/  /\ tasks[t].state = WAITING
                        /\ tasks' = [ tasks EXCEPT ![t].state = CANCELLED ]
                        /\ UNCHANGED << lock, waitQ >>
                    \/  /\ tasks[t].state = RESUME
                        /\  \/  /\ NextNonCancelled(t) # 0
                                /\ tasks' = [tasks EXCEPT ![t].state = CANCELLED,
                                                         ![NextNonCancelled(t)].state = RESUME ]
                                /\ waitQ' = SelectSeq(waitQ, LAMBDA x: x # t)
                                /\ UNCHANGED lock
                            \/  /\ NextNonCancelled(t) = 0
                                /\ CancelWhenWakeUp(t)

Bug1Next == \E t \in Tasks:
    \/ FixAcquire(t)
    \/ Release(t)
    \/ Resume(t)
    \/ CancelWhenWakeUp(t)
    \* \/ FixCancel(t)
    \/ Terminating

Bug1Spec == Init    /\ [][Bug1Next]_vars    \* need to specify faireness to rule out stuttering out of interest
                    /\ \A t \in Tasks:  /\ WF_vars(Release(t)) \* avoid stuttering: keep cancelling

\* Action property: ensure that cancel action is valid
CancelValid ==  /\ [][\A t \in 1..NTasks: FixCancel(t) => tasks'[t].state = CANCELLED]_<<vars>>
                \* /\ [][\A t \in 1..NTasks: WrongFixCancel(t) => tasks'[t].state # tasks[t].state ]_<<vars>>

=============================================================================
\* Modification History
\* Last modified Sun Apr 16 10:17:18 CST 2023 by haodu
\* Created Mon Apr 10 11:05:37 CST 2023 by haodu
