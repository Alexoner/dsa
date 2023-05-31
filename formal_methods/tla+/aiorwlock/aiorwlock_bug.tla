\* Original snapshot: https://github.com/aio-libs/aiorwlock/blob/b00c1090f2bb737873ae6f4b480c7e5740ffa3c3/aiorwlock/__init__.py
\* BUG: https://github.com/aio-libs/aiorwlock/pull/37
\* FIX PR: https://github.com/aio-libs/aiorwlock/pull/39/files
\* This specification reproduces the bug.
\* Note: this doesn't specify all behaviours of the implementation: minimal spec w.r.t State.
\*  - no wait for future, no notification for fairness of threads
\*  - self._owning abstracted as Lock state {"waiting", "Read", "WriteRead"}

(* Originall buggy implementation

# implementation based on:
# http://bugs.python.org/issue8800

# The internal lock object managing the RWLock state.
class _RWLockCore:

    def __init__(self, fast, loop):
        self._do_yield = not fast
        self._loop = loop or asyncio.get_event_loop()

        self._read_waiters = collections.deque()
        self._write_waiters = collections.deque()
        self._state = 0  # positive is shared count, negative exclusive count
        self._owning = []  # tasks will be few, so a list is not inefficient

    @property
    def read_locked(self):
        return self._state > 0

    @property
    def write_locked(self):
        return self._state < 0

    # Acquire the lock in read mode.
    @asyncio.coroutine
    def acquire_read(self):
        me = asyncio.Task.current_task(loop=self._loop)

        if me in self._owning:
            self._state += 1
            self._owning.append(me)
            if self._do_yield:
                yield from asyncio.sleep(0.0, loop=self._loop)
            return True

        if not self._write_waiters and self._state >= 0:
            self._state += 1
            self._owning.append(me)
            if self._do_yield:
                yield from asyncio.sleep(0.0, loop=self._loop)
            return True

        fut = create_future(self._loop)
        self._read_waiters.append(fut)
        try:
            yield from fut
            self._state += 1
            self._owning.append(me)
            return True
        finally:
            self._read_waiters.remove(fut)

    # Acquire the lock in write mode.  A 'waiting' count is maintain ed,
    # ensurring that 'readers' will yield to writers.
    @asyncio.coroutine
    def acquire_write(self):
        me = asyncio.Task.current_task(loop=self._loop)

        if me in self._owning:
            if self._state > 0:
                raise RuntimeError("cannot upgrade RWLock from read to write")
            self._state -= 1
            self._owning.append(me)
            if self._do_yield:
                yield from asyncio.sleep(0.0, loop=self._loop)
            return True

        if self._state == 0:
            self._state -= 1
            self._owning.append(me)
            if self._do_yield:
                yield from asyncio.sleep(0.0, loop=self._loop)
            return True

        fut = create_future(self._loop)
        self._write_waiters.append(fut)
        try:
            yield from fut
            self._state -= 1
            self._owning.append(me)
            return True
        finally:
            self._write_waiters.remove(fut)

    def release(self):
        me = asyncio.Task.current_task(loop=self._loop)
        try:
            self._owning.remove(me)
        except ValueError:
            raise RuntimeError("cannot release an un-acquired lock")
        if self._state > 0:
            self._state -= 1
        else:
            self._state += 1
        if self._state == 0:
            if self._write_waiters:
                self._write_waiters[0].set_result(None)
            elif self._read_waiters:
                self._read_waiters[0].set_result(None)

*)
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