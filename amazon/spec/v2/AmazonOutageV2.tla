---- MODULE AmazonOutageV2 ----
EXTENDS Naturals, Sequences

(*
V2: Control-plane vs Data-plane + request routing
Bug A: instance becomes Unhealthy but is still (re)Registered into data-plane pool,
so requests can be routed to it -> errors > 0.

UseBad chooses the trace.
Each event record has fields: t, type, id, az, req, target.
Unused fields are "".
*)

CONSTANT UseBad

TraceGood ==
<<
  [t |-> 0, type |-> "Launch",    id |-> "i1", az |-> "A", req |-> "",   target |-> ""],
  [t |-> 1, type |-> "Launch",    id |-> "i2", az |-> "B", req |-> "",   target |-> ""],

  [t |-> 2, type |-> "Healthy",   id |-> "i1", az |-> "",  req |-> "",   target |-> ""],
  [t |-> 3, type |-> "Healthy",   id |-> "i2", az |-> "",  req |-> "",   target |-> ""],

  [t |-> 4, type |-> "Register",  id |-> "i1", az |-> "",  req |-> "",   target |-> ""],
  [t |-> 5, type |-> "Register",  id |-> "i2", az |-> "",  req |-> "",   target |-> ""],

  [t |-> 6, type |-> "Propagate", id |-> "",   az |-> "",  req |-> "",   target |-> ""],
  [t |-> 7, type |-> "Request",   id |-> "",   az |-> "",  req |-> "r1", target |-> "i1"],

  [t |-> 8, type |-> "Unhealthy", id |-> "i1", az |-> "",  req |-> "",   target |-> ""],

  [t |-> 9, type |-> "Deregister",id |-> "i1", az |-> "",  req |-> "",   target |-> ""],
  [t |-> 10,type |-> "Propagate", id |-> "",   az |-> "",  req |-> "",   target |-> ""],

  [t |-> 11,type |-> "Request",   id |-> "",   az |-> "",  req |-> "r2", target |-> "i2"],
  [t |-> 12,type |-> "Terminate", id |-> "i1", az |-> "",  req |-> "",   target |-> ""]
>>

TraceBad ==
<<
  [t |-> 0, type |-> "Launch",    id |-> "i1", az |-> "A", req |-> "",   target |-> ""],
  [t |-> 1, type |-> "Launch",    id |-> "i2", az |-> "B", req |-> "",   target |-> ""],

  [t |-> 2, type |-> "Healthy",   id |-> "i1", az |-> "",  req |-> "",   target |-> ""],
  [t |-> 3, type |-> "Healthy",   id |-> "i2", az |-> "",  req |-> "",   target |-> ""],

  [t |-> 4, type |-> "Register",  id |-> "i1", az |-> "",  req |-> "",   target |-> ""],
  [t |-> 5, type |-> "Register",  id |-> "i2", az |-> "",  req |-> "",   target |-> ""],

  [t |-> 6, type |-> "Propagate", id |-> "",   az |-> "",  req |-> "",   target |-> ""],
  [t |-> 7, type |-> "Request",   id |-> "",   az |-> "",  req |-> "r1", target |-> "i1"],

  [t |-> 8, type |-> "Unhealthy", id |-> "i1", az |-> "",  req |-> "",   target |-> ""],

  \* Bug A: control-plane (re)registers i1 again (or never removed),
  \* and propagation makes data-plane still route to i1
  [t |-> 9, type |-> "Register",  id |-> "i1", az |-> "",  req |-> "",   target |-> ""],
  [t |-> 10,type |-> "Propagate", id |-> "",   az |-> "",  req |-> "",   target |-> ""],

  \* Request hits unhealthy instance -> error
  [t |-> 11,type |-> "Request",   id |-> "",   az |-> "",  req |-> "r2", target |-> "i1"]
>>

Trace == IF UseBad THEN TraceBad ELSE TraceGood

VARIABLES i,
          inst, healthy,
          controlPool, dataPool,
          blocked,
          azA, azB,
          errors

Init ==
  /\ i = 1
  /\ inst = {}
  /\ healthy = {}
  /\ controlPool = {}
  /\ dataPool = {}
  /\ blocked = {}
  /\ azA = {}
  /\ azB = {}
  /\ errors = 0

Step(e) ==
  CASE e.type = "Launch" ->
        /\ inst' = inst \cup {e.id}
        /\ IF e.az = "A" THEN azA' = azA \cup {e.id} ELSE azA' = azA
        /\ IF e.az = "B" THEN azB' = azB \cup {e.id} ELSE azB' = azB
        /\ UNCHANGED <<healthy, controlPool, dataPool, blocked, errors>>

  [] e.type = "Healthy" ->
        /\ e.id \in inst
        /\ healthy' = healthy \cup {e.id}
        /\ blocked' = blocked \ {e.id}
        /\ UNCHANGED <<inst, controlPool, dataPool, azA, azB, errors>>

  [] e.type = "Unhealthy" ->
        /\ e.id \in inst
        /\ healthy' = healthy \ {e.id}
        /\ blocked' = blocked \cup {e.id}
        /\ UNCHANGED <<inst, controlPool, dataPool, azA, azB, errors>>

  [] e.type = "Register" ->
        /\ e.id \in inst
        /\ controlPool' = controlPool \cup {e.id}
        /\ UNCHANGED <<inst, healthy, dataPool, blocked, azA, azB, errors>>

  [] e.type = "Deregister" ->
        /\ controlPool' = controlPool \ {e.id}
        /\ UNCHANGED <<inst, healthy, dataPool, blocked, azA, azB, errors>>

  [] e.type = "Propagate" ->
        /\ dataPool' = controlPool
        /\ UNCHANGED <<inst, healthy, controlPool, blocked, azA, azB, errors>>

  [] e.type = "Request" ->
        /\ LET tgt == e.target IN
           /\ IF (tgt \in dataPool) /\ (tgt \in healthy) THEN
                 errors' = errors
              ELSE
                 errors' = errors + 1
        /\ UNCHANGED <<inst, healthy, controlPool, dataPool, blocked, azA, azB>>

  [] e.type = "Terminate" ->
        /\ inst' = inst \ {e.id}
        /\ healthy' = healthy \ {e.id}
        /\ controlPool' = controlPool \ {e.id}
        /\ dataPool' = dataPool \ {e.id}
        /\ blocked' = blocked \ {e.id}
        /\ azA' = azA \ {e.id}
        /\ azB' = azB \ {e.id}
        /\ UNCHANGED errors

  [] OTHER ->
        /\ UNCHANGED <<inst, healthy, controlPool, dataPool, blocked, azA, azB, errors>>

Next ==
  IF i <= Len(Trace) THEN
    /\ LET e == Trace[i] IN Step(e)
    /\ i' = i + 1
  ELSE
    /\ UNCHANGED <<i, inst, healthy, controlPool, dataPool, blocked, azA, azB, errors>>

InvNoBadRoute ==
  errors = 0

InvPoolsWellFormed ==
  /\ controlPool \subseteq inst
  /\ dataPool \subseteq inst
  /\ azA \cap azB = {}
  /\ azA \cup azB \subseteq inst

Spec == Init /\ [][Next]_<<i,inst,healthy,controlPool,dataPool,blocked,azA,azB,errors>>

====
