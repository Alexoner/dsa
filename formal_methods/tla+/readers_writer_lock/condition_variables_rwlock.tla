\* https://en.wikipedia.org/wiki/Readers%E2%80%93writer_lock#Using_two_mutexes
\* begin read: 3 steps, lock & increament, lock g, unlock r
\* The readers writer lock implemented with condition variables: r, g.
\* NOTE: notify mechanism is expressed implicitly, assuming broadcast always works without any additional states!
\* condition variable: https://web.stanford.edu/~ouster/cgi-bin/cs140-spring14/lecture.php?topic=locks
\* simlification: condition variable signlaing just schedule waiting threads to execute, proceeding is controlled by actual condition.

\* Condition variables: used to wait for a particular condition to become true (e.g. characters in buffer).
\*  wait(condition, lock): release lock, put thread to sleep until condition is signaled; when thread wakes up again, re-acquire lock before returning.
\*  signal(condition, lock): if any threads are waiting on condition, wake up one of them. Caller must hold lock, which must be the same as the lock used in the wait call.
\*  broadcast(condition, lock): same as signal, except wake up all waiting threads.
\* Note: after signal, signaling thread keeps lock, waking thread goes on the queue waiting for the lock.
\* Warning: when a thread wakes up after cond_wait there is no guarantee that the desired condition still exists: another thread might have snuck in.

-------------------- MODULE condition_variables_rwlock --------------


EXTENDS Integers

CONSTANTS 
    Readers,
    Writers

VARIABLES
    \* r, \* mutex used by readers, protecting b
    g, \* global mutex, ensures mutual exclusion of writers
    pc, \* program counter
    num_readers_active, \* the number of readers that have acquired the lock (integer)
    num_writers_waiting,  \* the number of writers waiting for access (integer)
    writer_active \* whether a writer has acquired the lock (boolean).

vars == << g, pc, num_readers_active, num_writers_waiting, writer_active>>
-------------------------------
Init == /\ g = 0 \* unlocked
        /\ num_readers_active = 0
        /\ num_writers_waiting = 0
        /\ writer_active = 0
        /\ pc = [ x \in Readers \cup Writers |-> IF x \in Readers 
                        THEN "BeginReadLockG"
                        ELSE "BeginWriteLockG" ]

-------------------------------

BeginReadLockG(t) == /\ pc[t] = "BeginReadLockG"
                     /\ \/  /\ g = 0
                            /\ g' = t 
                            /\ pc' = [pc EXCEPT ![t] = "BeginReadWait"]
                            /\ UNCHANGED << num_readers_active, num_writers_waiting, writer_active >>

\* BeginReadIncrement(t) == \* Increment num_readers_active
\*     /\ pc[t] = "BeginReadIncrement"
\*     /\ num_writers_waiting <= 0 
\*     /\ writer_active = 0
\*     /\ num_readers_active' = num_readers_active + 1
\*     /\ pc' = [pc EXCEPT ![t] = "BeginReadUnlockG"]
\*     /\ UNCHANGED << g, num_writers_waiting, writer_active >>

BeginReadWait(t) == \* Increment num_readers_active
    /\ pc[t] = "BeginReadWait"
    /\  \/  /\ num_writers_waiting <= 0   \* condition met
            /\ writer_active = 0
            /\ num_readers_active' = num_readers_active + 1
            /\ g \in {0, t}
            /\ g' = t  \* must have acquired the lock. not exactly the same as condition variable
            /\ pc' = [pc EXCEPT ![t] = "BeginReadUnlockG"]
            /\ UNCHANGED << num_writers_waiting, writer_active >>
        \/  /\ num_writers_waiting > 0 \/ writer_active > 0  \* condition not met, unlock and sleep. TODO: assign lock?
            /\ g' = IF g = t THEN 0 ELSE g \* release lock if acquired, keep waiting
            /\ UNCHANGED << pc, num_readers_active, num_writers_waiting, writer_active >>

BeginReadUnlockG(t) ==  /\ pc[t] = "BeginReadUnlockG"
                        /\ g = t
                        /\ g' = 0
                        /\ pc' = [pc EXCEPT ![t] = "EndReadLockG"]
                        /\ UNCHANGED << num_readers_active, num_writers_waiting, writer_active >>

------------------------------------------------------------------------------------------------

EndReadLockG(t) == /\ pc[t] = "EndReadLockG"
                   /\ g = 0
                   /\ g' = t
                   /\ num_readers_active' = num_readers_active - 1 \* omitting the signal notify 
                   /\ pc' = [pc EXCEPT ![t] = "EndReadUnlockG"]
                   /\ UNCHANGED << num_writers_waiting, writer_active >>

EndReadUnlockG(t) == /\ pc[t] = "EndReadUnlockG"
                     /\ g = t 
                     /\ g' = 0
                     /\ pc' = [pc EXCEPT ![t] = "BeginReadLockG"]
                     /\ UNCHANGED << num_readers_active, num_writers_waiting, writer_active >>

------------------------------------------------------------------------------------------------

BeginWriteLockG(t) == /\ pc[t] = "BeginWriteLockG"
                      /\ g = 0
                      /\ g' = t
                      /\ num_writers_waiting' = num_writers_waiting + 1
                      /\ pc' = [pc EXCEPT ![t] = "BeginWriteWait"]
                      /\ UNCHANGED  << num_readers_active, writer_active >>

\* BeginWriteDecrement(t) == /\ pc[t] = "BeginWriteDecrement"
\*                           /\ num_readers_active = 0 /\ writer_active = 0\* enablling condition for wait cond, g
\*                           /\ num_writers_waiting' = num_writers_waiting - 1
\*                           /\ writer_active' = 1
\*                           /\ pc' = [pc EXCEPT ![t] = "BeginWriteUnlockG"]
\*                           /\ UNCHANGED  << g, num_readers_active >>

BeginWriteWait(t) == /\ pc[t] = "BeginWriteWait"
                     /\     \/  /\ num_readers_active = 0 /\ writer_active = 0 \* enablling condition for wait cond, g
                                /\ g \in {0, t}
                                /\ g' = t
                                /\ num_writers_waiting' = num_writers_waiting - 1
                                /\ writer_active' = 1
                                /\ pc' = [pc EXCEPT ![t] = "BeginWriteUnlockG"]
                                /\ UNCHANGED  << num_readers_active >>
                            \/  /\ num_readers_active > 0 \/ writer_active > 0 \* enabling condition for wait cond, g
                                /\ g' = IF g = t THEN 0 ELSE g \* release lock if acquired, keep waiting
                                /\ UNCHANGED << pc, num_readers_active, num_writers_waiting, writer_active >>

BeginWriteUnlockG(t) == /\ pc[t] = "BeginWriteUnlockG"
                        /\ g  = t 
                        /\ g' = 0
                        /\ pc' = [pc EXCEPT ![t] = "EndWriteLockG"]
                        /\ UNCHANGED << num_readers_active, num_writers_waiting, writer_active >>

------------------------------------------------------------------------------------------------  

EndWriteLockG(t) == /\ pc[t] = "EndWriteLockG"
                    /\ g = 0 
                    /\ g' = t
                    /\ writer_active' = 0
                    /\ pc' = [pc EXCEPT ![t] = "EndWriteUnlock"]
                    /\ UNCHANGED  << num_readers_active, num_writers_waiting >>

EndWriteUnlock(t) == /\ pc[t] = "EndWriteUnlock"
                     /\ g = t 
                     /\ g' = 0
                     /\ pc' = [pc EXCEPT ![t] = "BeginWriteLockG"]  \* or "finished"
                     /\ UNCHANGED << num_readers_active, num_writers_waiting, writer_active >>
------------------------------------------------------------------------------------------------

Terminating ==  /\ \A t \in Readers \cup Writers: pc[t] = "finished"
                /\ UNCHANGED vars

------------------------------------------------------------------------------------------------

\* multiple unlock can happen as an atomic event, unlike lock which must be separated into multiple steps

Next == \/ \E t \in Readers:    \/ BeginReadLockG(t) 
                                \* \/ BeginReadIncrement(t) 
                                \/ BeginReadWait(t)
                                \/ BeginReadUnlockG(t)
                                \/ EndReadLockG(t)
                                \/ EndReadUnlockG(t)
        \/ \E t \in Writers:    \/ BeginWriteLockG(t)
                                \* \/ BeginWriteDecrement(t)
                                \/ BeginWriteWait(t)
                                \/ BeginWriteUnlockG(t)
                                \/ EndWriteLockG(t)
                                \/ EndWriteUnlock(t)
        \/ Terminating

\* if specifying too many faireness here..
\* FIXME: TLC cannot handle the temporal formula because it exceeds the maximum supported size in disjunctive normal form. 
Spec == Init    
            /\ [][Next]_vars
            \* specify fairness to avoid meaningless infinite suttering
            /\ WF_vars(Next)  \* XXX: rule out indefinite crash: inifite stuttering after init
            /\ \A t \in Readers:    /\ WF_vars(BeginReadUnlockG(t))   \* unlock always eventually happens
                                    /\ WF_vars(EndReadUnlockG(t))
                                    /\ WF_vars(EndReadLockG(t))
                                    \* rule out reader starvation: all readers shall proceed
                                    /\ SF_vars(BeginReadLockG(t))
                                    /\ SF_vars(EndReadLockG(t))
            /\ \A x \in Writers:    /\ WF_vars(BeginWriteLockG(t))
                                    /\ WF_vars(BeginWriteUnlockG(t))
                                    /\ WF_vars(EndWriteLockG(t))
                                    /\ WF_vars(EndWriteUnlock(t))
                                    \* /\ SF_vars(BeginWriteWait(w))
            \* /\ \E << t1, t2 >> \in Readers \X Writers: /\ WF_vars(BeginReadLockR(t1) \/ BeginWriteLockG(t2))

-------------------------
\* invariant
TypeOK == /\ num_readers_active \in Nat
          /\ num_writers_waiting \in Nat
          /\ g \in Readers \cup Writers \cup {0}
          /\ pc \in [ Readers \cup Writers -> {
            "BeginReadLockG",
            \* "BeginReadIncrement", 
            "BeginReadWait",
            "BeginReadUnlockG", 
            "EndReadLockG", "EndReadUnlockG",
            "BeginWriteLockG", 
            \* "BeginWriteDecrement", 
            "BeginWriteWait",
            "BeginWriteUnlockG",
            "EndWriteLockG", "EndWriteUnlock",
            "finished"
            } ]

ExclusiveWrite == /\ \A <<w, t2>> \in Writers \X Readers: pc[w] \in {"BeginWriteUnLockG", "EndWriteUnLockG"} => pc[t2] \notin {"BeginReadUnLockG", "EndReadUnLockG"}
                  /\ \A w1, w2 \in Writers: w1 # w2 /\ pc[w1] \in {"BeginWriteUnLockG", "EndWriteUnLockG"} => pc[w2] \notin {"BeginWriteUnLockG", "EndWriteUnLockG"}

\* action property: x and x'
LockCantBeStolen == [][g # 0 => g' = 0]_g

\* temporal properties
MultipleReaders == <>(num_readers_active > 1) \* can support multiple readers read

\* no deadlock

\* specify liveness: read, write must happen
\* no starvation. TODO: refine the property checking.

NoReadStarvation == \A t \in Readers:   
                            \* /\ []<>(<<BeginReadLockG(t)>>_vars)
                            /\ []<>(<<EndReadLockG(t)>>_vars)
NoWriteStarvation == \A w \in Writers: []<>(<<BeginWriteLockG(w)>>_vars)

NoStarvation == 
    /\ NoReadStarvation
    /\ NoWriteStarvation

===========================