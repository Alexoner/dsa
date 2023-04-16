\* https://github.com/Alexander-N/tla-specs/tree/main/crdt-bug
\* source problem: https://twitter.com/martinkl/status/1327025979454263297


------------------------------ MODULE crdt_bug ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS
    Machines,
    Keys, 
    Values,
    \* operations
    SET,
    DELETE,
    \* limit
    MAX_CLOCK
    
VARIABLES
    values,
    clock,   \* global lamport timestamp
    messages \* message queue

vars == << values, clock, messages >>

--------------------------------------------------------------------------------    
Init == /\ values = [ x \in Machines |-> {} ]
        /\ clock = 1
        /\ messages = [ x \in Machines |-> <<>> ]

TypeOK ==   /\ values \in [ Machines -> Seq(Keys \X (0..MAX_CLOCK) \X Machines) ]     \* values[machine] is a set of tuple <t,k,v>
            /\ clock \in Nat
\*            /\ messages \in [ Machines -> ]

\*Read(self, k) == IF \E ktv \in values[self]: ktv[1] = k

--------------------------------------------------------------------------------                      

\* payload: tuple of  << t, k, v >>
DeliverSet(self, payload) == 
            /\ LET
\*                payload == Head(messages[self])
                t == payload[1]
                k == payload[2]
                v == payload[3]
                previous == { x \in values[self]: x[2] = k } 
                rhs == { x \in previous: x[1] < t }
                IN
                IF previous = rhs
                THEN
                    /\ PrintT (<<"previous = rhs", previous, rhs >>)
                    /\ values' = [ values EXCEPT ![self] = (values[self] \ previous) \cup {<< t, k, v >>}] 
                ELSE
                    UNCHANGED <<values>>

                    
DeliverDelete(self, payload) ==
\*        /\ LET payload == messages[self][1] IN
            /\ values' = [ values EXCEPT ![self] = {x \in values[self]: x[1] /= payload[1] }]

--------------------------------------------------------------------------------

\* FIXME[faireness]: always Delete? messages has infinite states of different length.
Broadcast(self, op, payload) ==
    /\ messages' = [ x \in Machines |-> Append(messages[x], <<op, payload>>) ]

BroadcastFair(self, op, payload) ==
    /\ PrintT( << "BroadcastFair", self, op, payload >>)
    /\  \/  /\ op = DELETE
            /\ DeliverDelete(self, payload)
        \/  /\ op = SET
            /\ DeliverSet(self, payload)
    /\ messages' = [ x \in Machines |-> IF x /= self THEN Append(messages[x], <<op, payload>>) ELSE messages[x] ]
                
Deliver(self) == 
    /\ messages[self] # <<>>
    /\ LET payload == Head(messages[self])
        IN
        /\  \/  /\ payload[1] = SET
                /\ DeliverSet(self, payload[2])
            \/  /\ payload[1] = DELETE
                /\ DeliverDelete(self, payload[2])
        /\ messages' = [ messages EXCEPT ![self] = Tail(messages[self]) ]
        /\ UNCHANGED << clock >>

--------------------------------------------------------------------------------                      

\* request to set, delete
RequestSet(self, k, v) ==
                /\ clock < MAX_CLOCK
                /\ clock' = clock + 1
                /\ BroadcastFair(self, SET, <<clock, k, v>>)
\*                /\ UNCHANGED values  \* disable this if values can change in BroadcastFair

RequestDelete(self, k) == 
        /\ \E <<t, k1, v>> \in values[self]: 
            /\ k1 = k
            /\ BroadcastFair(self, DELETE, <<t>>)
            /\ UNCHANGED << clock >>

----------------------------------------

Terminating ==  /\ clock = MAX_CLOCK
                /\ messages = [ m \in Machines |-> <<>> ] \*  all messages Deliverd by machines
\*                /\ values = [ m \in Machines |-> {} ]
                /\ UNCHANGED vars

----------------------------------------

Next == \/ \E self \in Machines:
            \/ \E k \in Keys:
                \/ \E v \in Values: RequestSet(self, k, v)
                \/ RequestDelete(self, k)
            \/ Deliver(self)
        \/ Terminating

Spec == Init    /\ [][Next]_vars
                /\ \A self \in Machines: 
                    /\ WF_vars(Deliver(self))    \* if message is sent, it's eventually Delivered

WrongSpec ==    /\ Spec 
                /\ \E << self, k >> \in Machines \X Keys: WF_vars(RequestDelete(self, k)) \* XXX: wrong, delete doesn't eventually happen! \E doesn't hide the bug though.
                /\ \A << self, k >> \in Machines \X Keys: WF_vars(RequestDelete(self, k)) \* XXX: this wrong faireness can hide the original bug!

---------------

AllValuesEqual == \A n1, n2 \in Machines:
        values[n1] = values[n2]
EventuallyConsistent == <>[]AllValuesEqual

=============================================================================
\* Modification History
\* Last modified Sat Apr 15 17:38:31 CST 2023 by haodu
\* Created Sat Apr 15 10:21:21 CST 2023 by haodu
