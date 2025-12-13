---- MODULE AmazonTraceValidator ----
EXTENDS Naturals, Sequences

(*
  Toy "Amazon outage" trace validation.
  UseBad selects which trace to validate.
  blocked models: "unhealthy happened and we haven't 'cleared' it via Deregister yet".
*)

CONSTANT UseBad

TraceGood ==
<<
  [t |-> 0, type |-> "Launch",     id |-> "i1"],
  [t |-> 1, type |-> "Healthy",    id |-> "i1"],
  [t |-> 2, type |-> "Register",   id |-> "i1"],
  [t |-> 3, type |-> "Unhealthy",  id |-> "i1"],
  [t |-> 4, type |-> "Deregister", id |-> "i1"],
  [t |-> 5, type |-> "Terminate",  id |-> "i1"]
>>

TraceBad ==
<<
  [t |-> 0, type |-> "Launch",     id |-> "i1"],
  [t |-> 1, type |-> "Healthy",    id |-> "i1"],
  [t |-> 2, type |-> "Register",   id |-> "i1"],
  [t |-> 3, type |-> "Unhealthy",  id |-> "i1"],
  [t |-> 4, type |-> "Register",   id |-> "i1"]  \* bug: unhealthy but (re)registered
>>

Trace == IF UseBad THEN TraceBad ELSE TraceGood

VARIABLES i, inst, healthy, pool, blocked

Init ==
  /\ i = 1
  /\ inst = {}
  /\ healthy = {}
  /\ pool = {}
  /\ blocked = {}

Step(e) ==
  CASE e.type = "Launch" ->
        /\ inst' = inst \cup {e.id}
        /\ UNCHANGED <<healthy, pool, blocked>>

  [] e.type = "Healthy" ->
        /\ e.id \in inst
        /\ healthy' = healthy \cup {e.id}
        /\ UNCHANGED <<inst, pool, blocked>>

  [] e.type = "Unhealthy" ->
        /\ e.id \in inst
        /\ healthy' = healthy \ {e.id}
        /\ pool' = pool \ {e.id}
        /\ blocked' = blocked \cup {e.id}
        /\ inst' = inst

  [] e.type = "Register" ->
        /\ e.id \in inst
        /\ pool' = pool \cup {e.id}
        /\ UNCHANGED <<inst, healthy, blocked>>

  [] e.type = "Deregister" ->
        /\ pool' = pool \ {e.id}
        /\ blocked' = blocked \ {e.id}
        /\ UNCHANGED <<inst, healthy>>

  [] e.type = "Terminate" ->
        /\ e.id \in inst
        /\ inst' = inst \ {e.id}
        /\ healthy' = healthy \ {e.id}
        /\ pool' = pool \ {e.id}
        /\ blocked' = blocked \ {e.id}

  [] OTHER ->
        /\ UNCHANGED <<inst, healthy, pool, blocked>>

Next ==
  IF i <= Len(Trace) THEN
    /\ LET e == Trace[i] IN Step(e)
    /\ i' = i + 1
  ELSE
    /\ UNCHANGED <<i, inst, healthy, pool, blocked>>

InvHealthy ==
  /\ pool \subseteq inst
  /\ pool \subseteq healthy

InvBlocked ==
  /\ pool \cap blocked = {}
  /\ blocked \subseteq inst

Spec == Init /\ [][Next]_<<i,inst,healthy,pool,blocked>>

====
