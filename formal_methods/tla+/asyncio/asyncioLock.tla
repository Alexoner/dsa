\* Specification of https://github.com/python/asyncio/blob/27218fa/asyncio/locks.py#L89-L201
\* has multiple bugs. Doesn't necessarily reproduce the original bug issue27585, since cancelling can happen any time!
\* To reproduce BUG: https://bugs.python.org/issue27585, refer to asyncioLock27585

\* reference: https://github.com/Alexander-N/tla-specs/tree/main/asyncio-lock

(* problematic code: https://github.com/python/asyncio/blob/27218fa/asyncio/locks.py#L89-L201 
class Lock(_ContextManagerMixin):
    """Primitive lock objects.
    A primitive lock is a synchronization primitive that is not owned
    by a particular coroutine when locked.  A primitive lock is in one
    of two states, 'locked' or 'unlocked'.
    It is created in the unlocked state.  It has two basic methods,
    acquire() and release().  When the state is unlocked, acquire()
    changes the state to locked and returns immediately.  When the
    state is locked, acquire() blocks until a call to release() in
    another coroutine changes it to unlocked, then the acquire() call
    resets it to locked and returns.  The release() method should only
    be called in the locked state; it changes the state to unlocked
    and returns immediately.  If an attempt is made to release an
    unlocked lock, a RuntimeError will be raised.
    When more than one coroutine is blocked in acquire() waiting for
    the state to turn to unlocked, only one coroutine proceeds when a
    release() call resets the state to unlocked; first coroutine which
    is blocked in acquire() is being processed.
    acquire() is a coroutine and should be called with 'yield from'.
    Locks also support the context management protocol.  '(yield from lock)'
    should be used as the context manager expression.
    Usage:
        lock = Lock()
        ...
        yield from lock
        try:
            ...
        finally:
            lock.release()
    Context manager usage:
        lock = Lock()
        ...
        with (yield from lock):
             ...
    Lock objects can be tested for locking state:
        if not lock.locked():
           yield from lock
        else:
           # lock is acquired
           ...
    """

    def __init__(self, *, loop=None):
        self._waiters = collections.deque()
        self._locked = False
        if loop is not None:
            self._loop = loop
        else:
            self._loop = events.get_event_loop()

    def __repr__(self):
        res = super().__repr__()
        extra = 'locked' if self._locked else 'unlocked'
        if self._waiters:
            extra = '{},waiters:{}'.format(extra, len(self._waiters))
        return '<{} [{}]>'.format(res[1:-1], extra)

    def locked(self):
        """Return True if lock is acquired."""
        return self._locked

    @coroutine
    def acquire(self):
        """Acquire a lock.
        This method blocks until the lock is unlocked, then sets it to
        locked and returns True.
        """
        if not self._waiters and not self._locked:
            self._locked = True
            return True

        fut = self._loop.create_future()
        self._waiters.append(fut)
        try:
            yield from fut
            self._locked = True
            return True
        finally:
            self._waiters.remove(fut)

    def release(self):
        """Release a lock.
        When the lock is locked, reset it to unlocked, and return.
        If any other coroutines are blocked waiting for the lock to become
        unlocked, allow exactly one of them to proceed.
        When invoked on an unlocked lock, a RuntimeError is raised.
        There is no return value.
        """
        if self._locked:
            self._locked = False
            # Wake up the first waiter who isn't cancelled.
            for fut in self._waiters:
                if not fut.done():
                    fut.set_result(True)
                    break
        else:
            raise RuntimeError('Lock is not acquired.')
*)

(* reproducing code: https://bugs.python.org/file44007/lock2.py
Note: 
    - awaiting asyncio.sleep() forces the async function to yield control to the event loop (even when the delay is 0)


import asyncio

async def v(n):
    for i in range(2):
        print(n, "Waiting for lock")
        async with lock:
            print(n, "Got lock")
            await f

async def test():
    f0 = asyncio.ensure_future(v(0))
    f1 = asyncio.ensure_future(v(1))
    await asyncio.sleep(0)
    f.set_result(True)
    f1.cancel()
    await f0

lock = asyncio.Lock()
f = asyncio.Future()
loop = asyncio.get_event_loop()
loop.run_until_complete(test())
*)

-------------------------- MODULE asyncioLock --------------------------

EXTENDS Integers, Sequences, Functions

CONSTANTS
    NTasks,
    \* process states
    RUNNING,
    WAITING,
    RESUME,  \* resume execution after yielding control in acquire
    CANCELLED,
    \* lock acquiring state
    ACQUIRED,
    RELEASED

VARIABLES
    lock,
    tasks,
    waitQ

------------------------------------------------
    
vars == << tasks, lock, waitQ >>

Tasks == 1..NTasks

Init == /\ tasks = [ x \in 1..NTasks |-> [state |-> RUNNING, lock |-> RELEASED ] ]
        /\ waitQ = <<>>
        /\ lock = 0 

TypeOK ==   /\ tasks \in [ Tasks -> [ state: { RUNNING, WAITING, RESUME, CANCELLED }, 
                                      lock: {ACQUIRED, RELEASED} ] ]
            /\ lock \in (1..NTasks \cup {0})  

--------------------------

\* wait happens within acquire, as state transition resulting from yielding control to other coroutine
Wait(t) ==  /\ UNCHANGED lock
            /\ waitQ' = Append(waitQ, t)
            /\ tasks' = [ tasks EXCEPT ![t].state = WAITING ]

Acquire(t) ==       \* acquire the lock or put to wait
                /\ tasks[t].state = RUNNING
                /\ tasks[t].lock = RELEASED
                /\  \/  /\ lock = 0       \* enabling condition disjunct: lock acquired by someone else
                        /\ waitQ = <<>>    
                        /\ lock' = t
                        /\ tasks' = [ tasks EXCEPT ![t].lock = ACQUIRED ] 
                        /\ UNCHANGED waitQ
                    \/  /\  \/ lock # 0
                            \/ waitQ # <<>>   \* wait in queued if locked or others waiting
                        /\ Wait(t)

\* resume execution after yielding in acquire 
Resume(t) ==    /\ tasks[t].state = RESUME
                /\ lock' = t
                /\ waitQ' = SelectSeq(waitQ, LAMBDA x: x # t)  \* BUG: taking tail
                /\ tasks' = [ tasks EXCEPT 
                              ![t].state = RUNNING,
                              ![t].lock = ACQUIRED]

--------------------------------

\* wakeup: resume execution of a coroutine after yielding control.
\* TODO: Wakeup happens in Release? 
\* TODO: coroutine guarantees release & assign lock to first waiting coroutine in the wait queue?
\*WakeUp(f, t) == /\ tasks[t].state = WAITING
\*                /\ lock' = t
\*                /\ waitQ' = Tail(waitQ)
\*                /\ tasks' = [ tasks EXCEPT 
\*                                ![t].state = RUNNING,
\*                                ![t].lock = ACQUIRED,
\*                                ![f].lock = RELEASED ]

\* use modular definition to make action expression simpler!!!
FirstNonCancelled ==  LET waitList == SelectSeq(waitQ, LAMBDA x: tasks[x].state # CANCELLED)
                      IN 
                        IF waitList = <<>>
                        THEN 0
                        ELSE Head(waitList)

Notify(f, t) ==     /\ tasks[t].state = WAITING
                    /\ lock' = 0
                    /\ tasks' = [tasks EXCEPT ![t].state = RESUME, ![f].lock = RELEASED]
                    /\ UNCHANGED <<waitQ>>

Release(t) ==   /\ tasks[t].state = RUNNING
                /\ tasks[t].lock = ACQUIRED
                /\ lock = t
                /\  IF FirstNonCancelled # 0 
                    THEN Notify(t, FirstNonCancelled) 
                    ELSE    /\ tasks' = [ tasks EXCEPT ![t].lock = RELEASED ] 
                            /\ lock' = 0
                            /\ UNCHANGED waitQ

Release1(t) ==   /\ tasks[t].state = RUNNING
                /\ tasks[t].lock = ACQUIRED
                /\ lock = t
                /\ \/   /\ FirstNonCancelled # 0
\*                        /\ WakeUp(t, FirstNonCancelled) 
                        /\ Notify(t, FirstNonCancelled)
                   \/   /\ FirstNonCancelled = 0  \* BUG: missed this
                        /\ tasks' = [ tasks EXCEPT ![t].lock = RELEASED ] 
                        /\ lock' = 0
                        /\ UNCHANGED waitQ

--------------------

\*cancel a running: lock release MAY be handled by context manager https://github.com/python/cpython/blob/main/Lib/asyncio/locks.py#L12-L20
\*cancel a waiting task: bug
\*cancel a task just woke up triggered by a lock release: bug
Cancel(t) ==    /\ tasks[t].state # CANCELLED
\*                /\ tasks[t].state \in { WAITING, RUNNING }
                /\ tasks' = [ tasks EXCEPT ![t].state = CANCELLED ]
                /\ UNCHANGED << lock, waitQ >>

--------------------

AllDone == /\ \A t \in Tasks: tasks[t].state = CANCELLED    
Terminating ==   /\ AllDone         \* avoid deadlock when terminated 
                /\ UNCHANGED vars

--------------------

Next == \E t \in Tasks:
    \/ Acquire(t)
    \/ Release(t)
    \/ Resume(t) 
\*    \/ Wait(t)
\*    \/ WakeUp(t)
    \/ Cancel(t)
    \/ Terminating  \* avoid deadlock when terminated    

Spec == Init    /\ [][Next]_vars  
                /\ \A t \in Tasks: \* specify faireness to rule out stuttering that violates action properties
                    /\ WF_vars(Acquire(t))
                    /\ WF_vars(Release(t))
                    /\ WF_vars(Resume(t))

----------------------------------------------------------------------

Consistent == lock # 0 => tasks[lock].lock = ACQUIRED \* /\ tasks[lock].state = RUNNING

MutualExclusive == 
\* There can not be two tasks holding the lock at the same time.
  \A t1, t2 \in 1..NTasks:
    ~ (t1 # t2 /\ tasks[t1].state = ACQUIRED /\ tasks[t2].state = ACQUIRED)

\* invariant: no deadlock. TODO: better name than WAITING?
\* terminated, or at least one task is running <=> all threads not cancelled are waiting
NoDeadlock == 
        \/ AllDone
        \/ \E t \in Tasks: tasks[t].state \in { RUNNING, RESUME }
\*        \/ waitQ = <<>>
\*        \/  /\ waitQ # <<>>
\*            /\ Range(waitQ) = { t \in 1..NTasks: tasks[t].state \notin {RUNNING, RESUME} }

-----------------------------------------------------------------
\* alternative to NoDeadlock invariant
\* If the lock is locked at some point it has to get unlocked eventually, or all tasks get cancelled.
LockGetsUnlocked ==
  lock # 0 /\ ~AllDone ~> lock = 0 \/ AllDone

\*TODO: add liveness properties for no deadlock
\*termporal properties for liveness
\* update no deadlock to liveness instead of safety invariant?
Liveness == 
\*            /\ ~AllDone => []<>(NoDeadlock)
            /\ []<>(NoDeadlock)
\*            /\ v # 0 ~> v
\*            /\ \A v \in (Nat \ {0}): lock = v ~> lock # v  \* If the lock is locked at some point it has to get unlocked eventually.
            

=============================================================================
\* Modification History
\* Last modified Sun Apr 16 10:11:50 CST 2023 by haodu
\* Created Mon Apr 10 10:15:18 CST 2023 by haodu
