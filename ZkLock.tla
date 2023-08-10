------------------------------- MODULE ZkLock -------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

VARIABLES requests, responses, lock, processes
vars == <<requests, responses, lock, processes>>
PIDSet == {"p1", "p2", "p3"}
NullPID == "null"
UniversalPIDSet == PIDSet \cup {NullPID}
MessageTypes == {"check", "create", "delete"}
ResponseTypes == {"data", "event"}
EventTypes == {"created", "deleted", "conflict"}
Response == [dest: PIDSet, type: ResponseTypes, content: UniversalPIDSet \cup EventTypes]
Request == [src: PIDSet, type: MessageTypes]

ProcessState == [id: PIDSet, acquired: {TRUE, FALSE}, waiting: {TRUE, FALSE}]
LockState == [owner: UniversalPIDSet, waiters: SUBSET PIDSet]

Range(T) == { T[x] : x \in DOMAIN T }

TypeOK ==
    /\ lock \in LockState
    /\ Range(processes) \in SUBSET ProcessState
    /\ requests \in SUBSET Request
    /\ responses \in SUBSET Response

NoLock ==
    \A p \in Range(processes): p.acquired = FALSE
    
LockInvariant ==
    \/ NoLock
    \/
        LET
            owners == {p \in Range(processes): p.acquired = TRUE}
        IN
        /\ \A o \in owners: 
            \/ o.id = lock.owner
            \/ \E m \in responses:
                /\ o.id = m.dest
                /\ m.type = "event"
                /\ m.content = "deleted"

WaiterIsAlive ==
    LET
        waiters == {p \in Range(processes): p.waiting = TRUE}
    IN
    \/ Cardinality(waiters) = 0
    \/ \A w \in waiters:
        \/ w.id \in lock.waiters
        \/ \E m \in requests: m.src = w.id
        \/ \E m \in responses: m.dest = w.id

NoPendingRelease(p) ==
    /\ \A m \in requests: 
        \/ m.src # p
        \/
            /\ m.src = p
            /\ m.type # "delete"
    /\ \A m \in responses: 
        \/ m.dest # p
        \/
            /\ m.dest = p
            /\
                \/ m.type # "event"
                \/ 
                    /\ m.type = "event"
                    /\ m.content # "deleted"

Init ==
    /\ requests = {}
    /\ responses = {}
    /\ lock = [owner |-> NullPID, waiters |-> {}]
    /\ processes = [pid \in PIDSet |-> [id |-> pid, acquired |-> FALSE, waiting |-> FALSE]]

Create(m) ==
    \/
        LET 
            waiters == lock.waiters
        IN
        /\ lock.owner = NullPID
        /\ lock' = [lock EXCEPT !.owner = m.src, !.waiters={}]
        /\ responses' =responses \cup {[dest |-> m.src, type |-> "data", content |-> m.src]} \cup Range([pid \in waiters |-> [dest |-> pid, type |-> "event", content |-> "created"]])
        /\ requests' = requests \ {m}
        /\ UNCHANGED <<processes>>
    \/
        /\ lock.owner # NullPID
        /\ responses' = responses \cup {[dest |-> m.src, type |-> "event", content |-> "conflict"]}
        /\ requests' = requests \ {m}
        /\ UNCHANGED <<lock, processes>>

CheckAndWatch(m) ==
    /\ responses' = responses \cup {[dest |-> m.src, type |-> "data", content |-> lock.owner]}
    /\ lock' = [lock EXCEPT !.waiters = @ \cup {m.src}]
    /\ requests' = requests \ {m}
    /\ UNCHANGED <<processes>>

Delete(m) ==
    LET
        waiters == lock.waiters
    IN
    /\ lock' = [lock EXCEPT !.owner = NullPID, !.waiters = {}]
    /\ responses' = responses \cup Range([pid \in waiters \cup {m.src} |-> [dest |-> pid, type |-> "event", content |-> "deleted"]])
    /\ requests' = requests \ {m}
    /\ UNCHANGED <<processes>>

ProcessRequest ==
    LET 
        m == CHOOSE r \in requests: TRUE
    IN
    \/
        /\ m.type = "check"
        /\ CheckAndWatch(m)
    \/
        /\ m.type = "create"
        /\ Create(m)
    \/
        /\ m.type = "delete"
        /\ Delete(m)

ProcessResponse ==
    LET
        m == CHOOSE r \in responses: TRUE
        process == CHOOSE p \in Range(processes): p.id = m.dest
    IN
    \/
        /\ m.type = "data"
        /\
            \/
                /\ m.content = m.dest
                /\ process.acquired = FALSE
                /\ processes' = [processes EXCEPT ![m.dest].waiting = FALSE, ![m.dest].acquired = TRUE]
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock>>
            \/
                /\ m.content = m.dest
                /\ process.acquired = TRUE
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
            \/
                /\ m.content = NullPID
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "create"]}
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<lock, processes>>
            \/ 
                /\ m.content # NullPID
                /\ m.content # m.dest
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
            \/ UNCHANGED vars
                            
    \/
        /\ m.type = "event"
        /\
            \/
                /\ m.content = "created"
                /\ process.acquired = FALSE
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "check"]}
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<lock, processes>>
            \/
                /\ m.content = "created"
                /\ process.acquired = TRUE
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
            \/
                /\ m.content = "conflict"
                /\ process.acquired = TRUE
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
            \/
                /\ m.content = "conflict"
                /\ process.acquired = FALSE
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "check"]}
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<lock, processes>>
            \/
                /\ m.content = "deleted"
                /\ process.acquired = FALSE
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "create"]}
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<lock, processes>>
            \/
                /\ m.content = "deleted"
                /\ process.acquired = TRUE
                /\ processes' = [processes EXCEPT ![m.dest].waiting = FALSE, ![m.dest].acquired = FALSE]
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<lock, requests>>
                
            \/ UNCHANGED vars
    \/ UNCHANGED vars

TryLock(p) ==
    /\ requests' = requests \cup {[src |-> p, type |-> "check"]}
    /\ processes' = [processes EXCEPT ![p].waiting = TRUE]
    /\ UNCHANGED <<responses, lock>>

TryRelease(p) ==
    /\ requests' = requests \cup {[src |-> p, type |-> "delete"]}
    /\ UNCHANGED <<responses, lock, processes>>
 
Next ==
    \/
        /\ \E p \in Range(processes): 
            /\ p.acquired = FALSE
            /\ \A r \in requests: r.src # p.id
        /\
            LET
                process == CHOOSE p \in Range(processes): 
                    /\ p.acquired = FALSE
                    /\ \A r \in requests: r.src # p.id
            IN
            TryLock(process.id)
    \/
        /\ \E p \in Range(processes): 
            /\ p.acquired = TRUE
            /\ \A r \in requests: r.src # p.id
            /\ NoPendingRelease(p.id)
        /\
            LET
                process == CHOOSE p \in Range(processes): 
                    /\ p.acquired = TRUE
                    /\ \A r \in requests: r.src # p.id
                    /\ NoPendingRelease(p.id)
            IN
            TryRelease(process.id)
    \/ 
        /\ Cardinality(responses) > 0
        /\ ProcessResponse
    \/
        /\ Cardinality(requests) > 0
        /\ ProcessRequest
    \/ UNCHANGED vars

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

=============================================================================
