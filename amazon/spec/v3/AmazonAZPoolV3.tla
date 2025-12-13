---- MODULE AmazonAZPoolV3 ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* v3 (robust cfg): Cross-AZ pool scheduling (trace-driven)                *)
(* - instances: AZ / capacity / priority-class                             *)
(* - control-plane pool vs data-plane pool (Sync)                           *)
(* - router schedules using ONLY dataPool (can be stale)                    *)
(* - local-first, fallback to remote AZ if local has no eligible instance   *)
(* - BUG in bad trace: stale dataPool still contains unhealthy instance     *)
(***************************************************************************)

CONSTANTS UseBad, RetryLimit

AZS  == {"A","B"}
INSTS == {"i1","i2","i3"}
REQS  == {"r1","r2","r3","r4"}

InstOrder  == <<"i1","i2","i3">>
DefaultInst == InstOrder[1]

(*
  priority: 1=high, 2=low
  Supports(x,r): instance priority <= request priority
    - high request(1) only goes to prio=1 instances
    - low request(2) goes to prio=1 or prio=2
*)

(*** Two traces: Good (PASS) / Bad (FAIL) *********************************)

TraceGood ==
<<
  [type |-> "Launch", id |-> "i1", az |-> "A", cap |-> 1, prio |-> 1],
  [type |-> "Launch", id |-> "i2", az |-> "B", cap |-> 2, prio |-> 1],
  [type |-> "Launch", id |-> "i3", az |-> "A", cap |-> 1, prio |-> 2],

  [type |-> "Healthy", id |-> "i1"],
  [type |-> "Healthy", id |-> "i2"],
  [type |-> "Healthy", id |-> "i3"],

  [type |-> "Register", id |-> "i1"],
  [type |-> "Register", id |-> "i2"],
  [type |-> "Register", id |-> "i3"],

  [type |-> "Sync"],

  [type |-> "Req", req |-> "r1", az |-> "A", prio |-> 2],
  [type |-> "Schedule", req |-> "r1"],
  [type |-> "Complete", req |-> "r1"],

  (* i1 unhealthy -> immediately deregister + sync, so dataPool no longer has i1 *)
  [type |-> "Unhealthy", id |-> "i1"],
  [type |-> "Deregister", id |-> "i1"],
  [type |-> "Sync"],

  (* r2 is high-prio from AZ A: local has only i3(prio=2) which cannot serve prio=1 -> fallback to i2 *)
  [type |-> "Req", req |-> "r2", az |-> "A", prio |-> 1],
  [type |-> "Schedule", req |-> "r2"],
  [type |-> "Complete", req |-> "r2"]
>>

TraceBad ==
<<
  [type |-> "Launch", id |-> "i1", az |-> "A", cap |-> 1, prio |-> 1],
  [type |-> "Launch", id |-> "i2", az |-> "B", cap |-> 2, prio |-> 1],
  [type |-> "Launch", id |-> "i3", az |-> "A", cap |-> 1, prio |-> 2],

  [type |-> "Healthy", id |-> "i1"],
  [type |-> "Healthy", id |-> "i2"],
  [type |-> "Healthy", id |-> "i3"],

  [type |-> "Register", id |-> "i1"],
  [type |-> "Register", id |-> "i2"],
  [type |-> "Register", id |-> "i3"],

  [type |-> "Sync"],

  [type |-> "Req", req |-> "r1", az |-> "A", prio |-> 2],
  [type |-> "Schedule", req |-> "r1"],
  [type |-> "Complete", req |-> "r1"],

  (* BUG: i1 becomes unhealthy, BUT we do NOT deregister/sync -> dataPool still contains i1 *)
  [type |-> "Unhealthy", id |-> "i1"],

  (* r2 high-prio from AZ A: local eligible set is {i1} only -> schedules onto unhealthy i1 -> FAIL *)
  [type |-> "Req", req |-> "r2", az |-> "A", prio |-> 1],
  [type |-> "Schedule", req |-> "r2"]
>>

Trace == IF UseBad THEN TraceBad ELSE TraceGood

(*** State *****************************************************************)

VARIABLES
  i,
  inst, azMap, capMap, prioMap,
  healthy, blocked,
  controlPool, dataPool,
  pending, active, target, origin, rprio,
  load, tries, errors

vars ==
  << i, inst, azMap, capMap, prioMap, healthy, blocked,
     controlPool, dataPool,
     pending, active, target, origin, rprio,
     load, tries, errors >>

(*** Helpers ***************************************************************)

Pos(x) == CHOOSE k \in 1..Len(InstOrder) : InstOrder[k] = x
Pick(S) == CHOOSE x \in S : \A y \in S : Pos(x) <= Pos(y)

HasCap(x) == load[x] < capMap[x]
Supports(x, r) == prioMap[x] <= rprio[r]

LocalCands(r) ==
  { x \in dataPool :
      azMap[x] = origin[r] /\ HasCap(x) /\ Supports(x, r) }

RemoteCands(r) ==
  { x \in dataPool :
      azMap[x] /= origin[r] /\ HasCap(x) /\ Supports(x, r) }

ReqsOn(x) == { r \in active : target[r] = x }

(*** Init ******************************************************************)

Init ==
  /\ i = 1
  /\ inst = {}
  /\ azMap   = [x \in INSTS |-> "A"]
  /\ capMap  = [x \in INSTS |-> 1]
  /\ prioMap = [x \in INSTS |-> 2]
  /\ healthy = {}
  /\ blocked = {}
  /\ controlPool = {}
  /\ dataPool    = {}
  /\ pending = {}
  /\ active  = {}
  /\ target  = [r \in REQS |-> DefaultInst]
  /\ origin  = [r \in REQS |-> "A"]
  /\ rprio   = [r \in REQS |-> 2]
  /\ load    = [x \in INSTS |-> 0]
  /\ tries   = [r \in REQS |-> 0]
  /\ errors  = 0

(*** Trace step ************************************************************)

TraceStep ==
  /\ i <= Len(Trace)
  /\ LET e == Trace[i] IN
     CASE
       e.type = "Launch" ->
         /\ e.id \in INSTS /\ e.az \in AZS /\ e.cap \in 1..3 /\ e.prio \in 1..2
         /\ inst'   = inst \cup {e.id}
         /\ azMap'  = [azMap  EXCEPT ![e.id] = e.az]
         /\ capMap' = [capMap EXCEPT ![e.id] = e.cap]
         /\ prioMap' = [prioMap EXCEPT ![e.id] = e.prio]
         /\ UNCHANGED << healthy, blocked, controlPool, dataPool,
                         pending, active, target, origin, rprio,
                         load, tries, errors >>

     [] e.type = "Healthy" ->
         /\ e.id \in INSTS
         /\ healthy' = healthy \cup {e.id}
         /\ blocked' = blocked \ {e.id}
         /\ UNCHANGED << inst, azMap, capMap, prioMap, controlPool, dataPool,
                         pending, active, target, origin, rprio,
                         load, tries, errors >>

     [] e.type = "Unhealthy" ->
         /\ e.id \in INSTS
         /\ healthy' = healthy \ {e.id}
         /\ blocked' = blocked \cup {e.id}
         /\ UNCHANGED << inst, azMap, capMap, prioMap, controlPool, dataPool,
                         pending, active, target, origin, rprio,
                         load, tries, errors >>

     [] e.type = "Register" ->
         /\ e.id \in INSTS
         /\ controlPool' = controlPool \cup {e.id}
         /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                         dataPool, pending, active, target, origin, rprio,
                         load, tries, errors >>

     [] e.type = "Deregister" ->
         /\ e.id \in INSTS
         /\ controlPool' = controlPool \ {e.id}
         /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                         dataPool, pending, active, target, origin, rprio,
                         load, tries, errors >>

     [] e.type = "Sync" ->
         /\ dataPool' = controlPool
         /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                         controlPool, pending, active, target, origin, rprio,
                         load, tries, errors >>

     [] e.type = "Req" ->
         /\ e.req \in REQS /\ e.az \in AZS /\ e.prio \in 1..2
         /\ pending' = pending \cup {e.req}
         /\ origin'  = [origin EXCEPT ![e.req] = e.az]
         /\ rprio'   = [rprio  EXCEPT ![e.req] = e.prio]
         /\ tries'   = [tries  EXCEPT ![e.req] = 0]
         /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                         controlPool, dataPool, active, target,
                         load, errors >>

     [] e.type = "Schedule" ->
         /\ e.req \in pending
         /\ LET local == LocalCands(e.req) IN
            LET rem   == RemoteCands(e.req) IN
            LET cands == IF local # {} THEN local ELSE rem IN
              /\ IF cands = {} THEN
                    /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                                   controlPool, dataPool, pending, active, target,
                                   origin, rprio, load, tries, errors >>
                 ELSE
                    /\ LET x == Pick(cands) IN
                       /\ pending' = pending \ {e.req}
                       /\ active'  = active \cup {e.req}
                       /\ target'  = [target EXCEPT ![e.req] = x]
                       /\ load'    = [load   EXCEPT ![x] = @ + 1]
                       /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                                       controlPool, dataPool, origin, rprio, tries, errors >>

     [] e.type = "Complete" ->
         /\ e.req \in active
         /\ LET x == target[e.req] IN
            /\ load[x] > 0
            /\ active' = active \ {e.req}
            /\ load'   = [load EXCEPT ![x] = @ - 1]
            /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                            controlPool, dataPool, pending, target, origin, rprio,
                            tries, errors >>

     [] e.type = "Error" ->
         /\ e.req \in active
         /\ LET x == target[e.req] IN
            /\ load[x] > 0
            /\ active' = active \ {e.req}
            /\ load'   = [load EXCEPT ![x] = @ - 1]
            /\ errors' = errors + 1
            /\ tries'  = [tries EXCEPT ![e.req] =
                           IF @ < RetryLimit THEN @ + 1 ELSE @ ]
            /\ pending' =
                IF tries[e.req] < RetryLimit THEN pending \cup {e.req} ELSE pending
            /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                            controlPool, dataPool, target, origin, rprio >>

     [] OTHER ->
         /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                         controlPool, dataPool, pending, active, target, origin, rprio,
                         load, tries, errors >>

  /\ i' = i + 1

Stutter ==
  /\ i > Len(Trace)
  /\ UNCHANGED vars

Next == TraceStep \/ Stutter
Spec == Init /\ [][Next]_vars

(*** Invariants ************************************************************)

TypeOK ==
  /\ i \in Nat
  /\ inst \subseteq INSTS
  /\ azMap   \in [INSTS -> AZS]
  /\ capMap  \in [INSTS -> Nat]
  /\ prioMap \in [INSTS -> 1..2]
  /\ healthy \subseteq INSTS
  /\ blocked \subseteq INSTS
  /\ controlPool \subseteq inst
  /\ dataPool    \subseteq inst
  /\ pending \subseteq REQS
  /\ active  \subseteq REQS
  /\ pending \cap active = {}
  /\ target \in [REQS -> INSTS]
  /\ origin \in [REQS -> AZS]
  /\ rprio  \in [REQS -> 1..2]
  /\ load   \in [INSTS -> Nat]
  /\ tries  \in [REQS -> Nat]
  /\ errors \in Nat

InvLoadCap ==
  \A x \in INSTS : load[x] <= capMap[x]

InvLoadConsistent ==
  \A x \in INSTS : load[x] = Cardinality(ReqsOn(x))

InvNoGhostLoad ==
  \A x \in (INSTS \ inst) : load[x] = 0

InvActiveTargetExists ==
  \A r \in active : target[r] \in inst

InvRetryBound ==
  \A r \in REQS : tries[r] <= RetryLimit

InvNoBadRoute ==
  \A r \in active :
    /\ target[r] \in healthy
    /\ target[r] \notin blocked

InvFallbackSound ==
  \A r \in active :
    LET tgtAZ == azMap[target[r]] IN
      (tgtAZ /= origin[r]) => (LocalCands(r) = {})

=============================================================================
