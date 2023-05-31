------------------------------ MODULE crdt_fix ------------------------------
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

crdt_bug == INSTANCE crdt_bug
\* Broadcast(self, op, payload) == crdt_bug!Broadcast(self, op, payload)
\* BroadcastFair(self, op, payload) == crdt_bug!BroadcastFair(self, op, payload)
Init == crdt_bug!Init
TypeOK == crdt_bug!TypeOK

Terminating == crdt_bug!Terminating
EventuallyConsistent  == crdt_bug!EventuallyConsistent


--------------------------------------------------------------------------------    

\* payload: tuple of  << t, k, v >>
DeliverSet(self, payload) == 
            /\ LET
                t == payload[1]
                k == payload[2]
                v == payload[3]
                T == payload[4]
                IN
                values' = [ values EXCEPT ![self] = 
                            { << t1, k1, v1 >> \in values[self]: t1 \notin T } \cup {<<t, k, v>>}
                          ]

DeliverDelete(self, payload) ==
    LET T == payload[1] IN 
    /\ values' = [ values EXCEPT ![self] = {<<t, k, v>> \in values[self]: t \notin T }]

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

                   
-------------

\* request to set, delete
RequestSet(self, k, v) ==
                /\ clock < MAX_CLOCK
                /\ clock' = clock + 1
                /\  LET 
                        matches == { << t, k1, v1 >> \in values[self]: k1 = k}
                        T == { t: <<t, k1, v1>> \in matches } \* NOTE: the grammar
                    IN 
                        /\ BroadcastFair(self, SET, <<clock, k, v, T>>)

RequestDelete(self, k) == 
        \* /\ \E <<t, k1, v>> \in values[self]: 
            \* /\ k1 = k
            /\ LET T == { t: <<t, k1, v>> \in values[self] } IN
                IF T # {}
                THEN 
                    /\ BroadcastFair(self, DELETE, <<T>>)
                    /\ UNCHANGED << clock >>
                ELSE
                    /\ FALSE

--------------------------------------

Next ==  
        \/ \E self \in Machines:
            \/ \E k \in Keys:
                \/ \E v \in Values: RequestSet(self, k, v)
                \/ RequestDelete(self, k)
            \/ Deliver(self)
        \/ Terminating

Spec == Init    /\ [][Next]_vars
                /\ \A self \in Machines: 
                    /\ WF_vars(Deliver(self))    \* if message is sent, it's eventually Deliverd


=============================================================================