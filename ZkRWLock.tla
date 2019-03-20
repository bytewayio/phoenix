(*
Writer:
    1. Check WLNode
        a. Node exists -> Wait and go to 2
        b. Node does not exist -> 2
    2. Create WLNode
        a. Node conflict -> Wait and go to 1
        b. Node created -> 3
    3. Check RLWaiter
        a. No Child -> Acquired
        b. Has Children -> Wait and go to 3
Reader:
    1. Create RLWaiter
        a. Success -> go to 2
    2. Check WLNode
        a. Node exists -> go to 3
        b. Node does not exist -> Acquired
    3. Delete RLWaiter
        a. Success -> wait and go to 1
*)
------------------------------- MODULE ZkRWLock -------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

VARIABLES requests, responses, lock, processes
vars == <<requests, responses, lock, processes>>
PIDSet == {"p1", "p2", "p3", "p4"}
NullPID == "null"
UniversalPIDSet == PIDSet \cup {NullPID}
LockTypes == {"None", "RLock", "WLock"}
NodeTypes == {"WLNode", "RLWaiter"}
Steps == {0, 1, 2, 3}

MessageTypes == {"check", "create", "delete"}
ResponseTypes == {"data", "event"}
EventTypes == {"created", "deleted", "conflict"}
Response == [dest: PIDSet, type: ResponseTypes, node: NodeTypes, content: UniversalPIDSet \cup EventTypes \cup {"zero", "nonzero"}]
Request == [src: PIDSet, type: MessageTypes, node: NodeTypes]

ProcessState == [id: PIDSet, wlockAcquired: {TRUE, FALSE}, rlockAcquired: {TRUE, FALSE}, pending: LockTypes, step: Steps]
LockState == [writer: UniversalPIDSet, readers: SUBSET PIDSet, writerWaiters: SUBSET PIDSet, readerWaiters: SUBSET PIDSet]

Range(T) == { T[x] : x \in DOMAIN T }

TypeOK ==
    /\ lock \in LockState
    /\ Range(processes) \in SUBSET ProcessState
    /\ requests \in SUBSET Request
    /\ responses \in SUBSET Response

NoReader ==
    \A p \in Range(processes): p.rlockAcquired = FALSE

NoWriter == 
    \A p \in Range(processes): p.wlockAcquired = FALSE
    
LockInvariant ==
    \/ NoWriter
    \/
        LET
            writers == {p \in Range(processes): p.wlockAcquired = TRUE}
            readers == {p \in Range(processes): p.rlockAcquired = TRUE}
        IN
        /\ \A w \in writers: 
            \/ w.id = lock.writer
            \/ \E m \in responses:
                /\ w.id = m.dest
                /\ m.type = "event"
                /\ m.node = "WLNode"
                /\ m.content = "deleted"
        /\
            \/ Cardinality(writers) = 0 \* duplicate logic, for readibilty purpose
            \/ Cardinality(readers) = 0 \* the unique of writer is ensure in w.id = lock.writer above
            \/ \A r \in readers:
                \/ \E m \in responses:
                    /\ r.id = m.dest
                    /\ m.type = "event"
                    /\ m.node = "RLWaiter"
                    /\ m.content = "deleted"

WaiterIsAlive ==
    LET
        waiters == {p \in Range(processes): p.pending \in {"RLock", "WLock"}}
    IN
    \/ Cardinality(waiters) = 0
    \/ \A w \in waiters:
        \/ w.id \in lock.writerWaiters \cup lock.readerWaiters
        \/ \E m \in requests: m.src = w.id
        \/ \E m \in responses: m.dest = w.id

NoPendingRelease(p, n) ==
    /\ \A m \in requests: 
        \/ m.src # p
        \/ 
            /\ m.src = p
            /\ m.node # n
        \/
            /\ m.src = p
            /\ m.node = n
            /\ m.type # "delete"
    /\ \A m \in responses: 
        \/ m.dest # p
        \/
            /\ m.dest = p
            /\ m.node # n
        \/
            /\ m.dest = p
            /\ m.node = n
            /\
                \/ m.type # "event"
                \/ 
                    /\ m.type = "event"
                    /\ m.content # "deleted"

Init ==
    /\ requests = {}
    /\ responses = {}
    /\ lock = [writer |-> NullPID, readers |-> {}, writerWaiters |-> {}, readerWaiters |-> {}]
    /\ processes = [pid \in PIDSet |-> [id |-> pid, wlockAcquired |-> FALSE, rlockAcquired |-> FALSE, pending |-> "None", step |-> 0]]

Create(m) ==
    \/ 
        /\ m.node = "WLNode"
        /\
            \/
                LET 
                    waiters == lock.writerWaiters
                IN
                /\ lock.writer = NullPID
                /\ lock' = [lock EXCEPT !.writer = m.src, !.writerWaiters={}]
                /\ responses' = responses \cup {[dest |-> m.src, node |-> "WLNode", type |-> "data", content |-> m.src]} \cup Range([pid \in waiters |-> [dest |-> pid, node |-> "WLNode", type |-> "event", content |-> "created"]])
                /\ requests' = requests \ {m}
                /\ UNCHANGED <<processes>>
            \/
                /\ lock.writer # NullPID
                /\ responses' = responses \cup {[dest |-> m.src, node |-> "WLNode", type |-> "event", content |-> "conflict"]}
                /\ requests' = requests \ {m}
                /\ UNCHANGED <<lock, processes>>
    \/
        LET
            waiters == lock.readerWaiters
        IN
        /\ m.node = "RLWaiter"
        /\ lock' = [lock EXCEPT !.readers = @ \cup {m.src}, !.readerWaiters = {}]
        /\ responses' = responses \cup {[dest |-> m.src, node |-> "RLWaiter", type |-> "data", content |-> m.src]} \cup Range([pid \in waiters |-> [dest |-> pid, node |-> "RLWaiter", type |-> "event", content |-> "created"]])
        /\ requests' = requests \ {m}
        /\ UNCHANGED <<processes>>
 
CheckAndWatch(m) ==
    /\ responses' = responses \cup {[dest |-> m.src, type |-> "data", node |-> m.node, content |-> IF m.node = "WLNode" THEN lock.writer ELSE IF Cardinality(lock.readers) = 0 THEN "zero" ELSE "nonzero"]}
    /\ lock' = [lock EXCEPT !.writerWaiters = IF m.node = "WLNode" THEN @ \cup {m.src} ELSE @, !.readerWaiters = IF m.node = "RLWaiter" THEN @ \cup {m.src} ELSE @]
    /\ requests' = requests \ {m}
    /\ UNCHANGED <<processes>>

Delete(m) ==
    LET
        waiters == IF m.node = "WLNode" THEN lock.writerWaiters ELSE lock.readerWaiters
    IN
    /\ lock' = [lock EXCEPT !.writer = IF m.node = "WLNode" THEN NullPID ELSE @, !.readers = IF m.node = "RLWaiter" THEN @ \ {m.src} ELSE @, !.readerWaiters = IF m.node = "RLWaiter" THEN {} ELSE @, !.writerWaiters = IF m.node = "WLNode" THEN {} ELSE @]
    /\ responses' = responses \cup Range([pid \in waiters \cup {m.src} |-> [dest |-> pid, type |-> "event", node |-> m.node, content |-> "deleted"]])
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
    \/ \*Writer behavior
        /\ process.pending = "WLock"
        /\ process.step = 1
        /\
            \/
                /\ m.node = "RLWaiter"
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
            \/
                /\ m.node = "WLNode"
                /\ m.type = "event"
                /\ m.content \in {"created", "deleted"}
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "check", node |-> "WLNode"]}
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<lock, processes>>
            \/
                /\ m.node = "WLNode"
                /\ m.type = "data"
                /\
                    \/
                        /\ m.content = NullPID
                        /\ processes' = [processes EXCEPT ![m.dest].step = 2]
                        /\ responses' = responses \ {m}
                        /\ requests' = requests \cup {[src |-> m.dest, type |-> "create", node |-> "WLNode"]}
                        /\ UNCHANGED <<lock>>
                    \/
                        /\ m.content # NullPID
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<requests, lock, processes>>
    \/
        /\ process.pending = "WLock"
        /\ process.step = 2
        /\
            \/
                /\ m.node = "RLWaiter"
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
            \/
                /\ m.node = "WLNode"
                /\ m.type = "event"
                /\
                    \/ 
                        /\ m.content = "conflict"
                        /\ requests' = requests \cup {[src |-> m.dest, type |-> "check", node |-> "WLNode"]}
                        /\ processes' = [processes EXCEPT ![m.dest].step = 1]
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<lock>>
                    \/
                        /\ m.content # "conflict"
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<requests, lock, processes>>
            \/
                /\ m.node = "WLNode"
                /\ m.type = "data"
                /\ m.content = m.dest
                /\ processes' = [processes EXCEPT ![m.dest].step = 3]
                /\ responses' = responses \ {m}
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "check", node |-> "RLWaiter"]}
                /\ UNCHANGED <<lock>>
    \/
        /\ process.pending = "WLock"
        /\ process.step = 3
        /\
            \/
                /\ m.node = "RLWaiter"
                /\ m.type = "data"
                /\ 
                    \/
                        /\ m.content = "zero"
                        /\ processes' = [processes EXCEPT ![m.dest].wlockAcquired = TRUE, ![m.dest].step = 0, ![m.dest].pending = "None"]
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<requests, lock>>
                    \/
                        /\ m.content = "nonzero"
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<requests, lock, processes>>
            \/
                /\ m.node = "RLWaiter"
                /\ m.type = "event"
                /\ m.content \in {"created", "deleted"}
                /\ responses' = responses \ {m}
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "check", node |-> "RLWaiter"]}
                /\ UNCHANGED <<lock, processes>>
            \/
                /\ m.node = "WLNode"
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
    \/
        /\ process.wlockAcquired = TRUE
        /\
            \/
                /\ m.node = "WLNode"
                /\ m.type = "event"
                /\
                    \/ 
                        /\ m.content = "deleted"
                        /\ processes' = [processes EXCEPT ![m.dest].wlockAcquired = FALSE]
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<requests, lock>>
                    \/
                        /\ m.content # "deleted"
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<requests, lock, processes>>
            \/
                /\ m.node = "RLWaiter"
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
    \/ \* Reader behavior 
        /\ process.pending = "RLock"
        /\ process.step = 1
        /\
            \/
                /\ m.node = "RLWaiter"
                /\ m.type = "data"
                /\ m.content = m.dest
                /\ processes' = [processes EXCEPT ![m.dest].step = 2]
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "check", node |-> "WLNode"]}
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<lock>>
            \/
                /\ m.node = "WLNode"
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
    \/
        /\ process.pending = "RLock"
        /\ process.step = 2
        /\
            \/
                /\ m.node = "WLNode"
                /\ m.type = "data"
                /\
                    \/
                        /\ m.content = NullPID
                        /\ processes' = [processes EXCEPT ![m.dest].step = 0, ![m.dest].rlockAcquired = TRUE, ![m.dest].pending = "None"]
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<requests, lock>>
                    \/
                        /\ m.content # NullPID
                        /\ requests' = requests \cup {[src |-> m.dest, type |-> "delete", node |-> "RLWaiter"]}
                        /\ responses' = responses \ {m}
                        /\ UNCHANGED <<lock, processes>>
            \/
                /\ m.node = "WLNode"
                /\ m.type = "event"
                /\ responses' = responses \ {m}
                /\ processes' = [processes EXCEPT ![m.dest].step = 3]
                /\ UNCHANGED <<requests, lock>>
            \/
                /\ m.node = "RLWaiter"
                /\ m.type = "event"
                /\ m.content = "deleted"
                /\ responses' = responses \ {m}
                /\ processes' = [processes EXCEPT ![m.dest].step = 3]
                /\ UNCHANGED <<requests, lock>>
    \/
        /\ process.pending = "RLock"
        /\ process.step = 3
        /\
            \/
                /\ m.node = "RLWaiter"
                /\ m.type = "event"
                /\ m.content = "deleted"
                /\ responses' = responses \ {m}
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "create", node |-> "RLWaiter"]}
                /\ processes' = [processes EXCEPT ![m.dest].step = 1]
                /\ UNCHANGED <<lock>>
            \/
                /\ m.node = "WLNode"
                /\ m.type = "event"
                /\ m.content \in {"deleted", "created"}
                /\ responses' = responses \ {m}
                /\ requests' = requests \cup {[src |-> m.dest, type |-> "create", node |-> "RLWaiter"]}
                /\ processes' = [processes EXCEPT ![m.dest].step = 1]
                /\ UNCHANGED <<lock>>
            \/
                /\ m.node = "WLNode"
                /\ m.type = "data"
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>
    \/
        /\ process.rlockAcquired = TRUE
        /\
            \/
                /\ m.node = "RLWaiter"
                /\ m.type = "event"
                /\ m.content = "deleted"
                /\ processes' = [processes EXCEPT ![m.dest].rlockAcquired = FALSE]
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock>>
            \/
                /\ m.node = "WLNode"
                /\ responses' = responses \ {m}
                /\ UNCHANGED <<requests, lock, processes>>

TryRLock(p) ==
    /\ requests' = requests \cup {[src |-> p, type |-> "create", node |-> "RLWaiter"]}
    /\ processes' = [processes EXCEPT ![p].pending = "RLock", ![p].step = 1]
    /\ UNCHANGED <<responses, lock>>

TryWLock(p) ==
    /\ requests' = requests \cup {[src |-> p, type |-> "check", node |-> "WLNode"]}
    /\ processes' = [processes EXCEPT ![p].pending = "WLock", ![p].step = 1]
    /\ UNCHANGED <<responses, lock>>

TryRelease(p) ==
    /\ requests' = requests \cup {[src |-> p, type |-> "delete", node |-> IF processes[p].rlockAcquired = TRUE THEN "RLWaiter" ELSE "WLNode" ]}
    /\ UNCHANGED <<responses, lock, processes>>
 
Next ==
    \/
        /\ \E p \in {processes["p1"], processes["p2"]}: 
            /\ p.rlockAcquired = FALSE
            /\ p.wlockAcquired = FALSE
            /\ p.pending = "None"
            /\ \A r \in requests: r.src # p.id
        /\
            LET
                process == CHOOSE p \in {processes["p1"], processes["p2"]}: 
                    /\ p.rlockAcquired = FALSE
                    /\ p.wlockAcquired = FALSE
                    /\ p.pending = "None"
                    /\ \A r \in requests: r.src # p.id
            IN
            TryWLock(process.id)
    \/
        /\ \E p \in {processes["p3"], processes["p4"]}: 
            /\ p.rlockAcquired = FALSE
            /\ p.wlockAcquired = FALSE
            /\ p.pending = "None"
            /\ \A r \in requests: r.src # p.id
        /\
            LET
                process == CHOOSE p \in {processes["p3"], processes["p4"]}: 
                    /\ p.rlockAcquired = FALSE
                    /\ p.wlockAcquired = FALSE
                    /\ p.pending = "None"
                    /\ \A r \in requests: r.src # p.id
            IN
            TryRLock(process.id)
    \/
        /\ \E p \in Range(processes): 
            /\ p.wlockAcquired = TRUE
            /\ \A r \in requests: r.src # p.id
            /\ NoPendingRelease(p.id, "WLNode")
        /\
            LET
                process == CHOOSE p \in Range(processes): 
                    /\ p.wlockAcquired = TRUE
                    /\ \A r \in requests: r.src # p.id
                    /\ NoPendingRelease(p.id, "WLNode")
            IN
            TryRelease(process.id)
    \/
        /\ \E p \in Range(processes): 
            /\ p.rlockAcquired = TRUE
            /\ \A r \in requests: r.src # p.id
            /\ NoPendingRelease(p.id, "RLWaiter")
        /\
            LET
                process == CHOOSE p \in Range(processes): 
                    /\ p.rlockAcquired = TRUE
                    /\ \A r \in requests: r.src # p.id
                    /\ NoPendingRelease(p.id, "RLWaiter")
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

=============================================================================
