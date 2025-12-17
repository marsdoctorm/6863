---- MODULE AmazonAZPoolV3 ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* v3 (robust cfg): Cross-AZ pool scheduling (trace-driven)                *)
(* - instances: AZ / capacity / priority-class                             *)
(* - control-plane pool vs data-plane pool (Sync)                           *)
(* - router schedules using ONLY dataPool (can be stale)                    *)
(* - local-first, fallback to remote AZ if local has no eligible instance   *)
(* - BUG in bad trace: stale dataPool still contains unhealthy instance     *)
(* - enhancements:
   - inventory-aware scheduling for low-priority requests (prefer prio=2 instances)
   - cross-AZ fallback budget guard + invariant
   - documented probabilistic failure knobs (as percentages 0..100; modeled via nondeterminism/trace)
   - static BackupMap for cross-AZ disaster recovery reasoning (checked via invariant)
*)
(***************************************************************************)

CONSTANTS UseBad, RetryLimit,
          FallbackBudget,
          P_DeliveryFail, P_NetworkDelay, P_LBFail,
          BackupMap

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
  [type |-> "Complete", req |-> "r2"],

  (* r3: 低优请求在本地(i3)失败一次 -> 隔离i3并同步 -> 重试跨AZ兜底到i2 完成 *)
  [type |-> "Req",        req |-> "r3", az |-> "A", prio |-> 2],
  [type |-> "Schedule",   req |-> "r3"],
  [type |-> "Error",      req |-> "r3"],   \* 可视为一次交付失败（现实里概率约 P_DeliveryFail%）
  [type |-> "Deregister", id  |-> "i3"],
  [type |-> "Sync"],
  [type |-> "Schedule",   req |-> "r3"],
  [type |-> "Complete",   req |-> "r3"]
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

MustCover ==
  {"Launch","Register","Req","Schedule","Complete","Error","Deregister","Sync","Unhealthy"}

TraceEventTypes == { Trace[k].type : k \in 1..Len(Trace) }

InvTraceCovers == MustCover \subseteq TraceEventTypes
  \* “覆盖率”约束：确保当前 Trace 至少覆盖关键分支事件类型（便于写报告/对照 Coverage 输出）


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

RemoteActiveCount == Cardinality({ r \in active : azMap[target[r]] /= origin[r] })

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
            LET localPref ==
              IF rprio[e.req] = 2 /\ (\E x \in local : prioMap[x] = 2)
              THEN { x \in local : prioMap[x] = 2 }   \* 低优请求优先占用低优实例
              ELSE local
            LET remPref ==
              IF rprio[e.req] = 2 /\ (\E x \in rem : prioMap[x] = 2)
              THEN { x \in rem : prioMap[x] = 2 }     \* 远端同样优先低优实例（若存在）
              ELSE rem
            LET budgetOK == (RemoteActiveCount < FallbackBudget) IN
            LET cands ==
              IF localPref # {} THEN localPref
              ELSE IF budgetOK THEN remPref ELSE {} IN
              /\ IF cands = {} THEN
                    /\ UNCHANGED << inst, azMap, capMap, prioMap, healthy, blocked,
                                   controlPool, dataPool, pending, active, target,
                                   origin, rprio, load, tries, errors >>
                    \* 无候选：可视为 LB 未找到可服务实例（现实里概率约 P_LBFail%）
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

  /\ BackupMap \in [INSTS -> INSTS]
  /\ FallbackBudget \in Nat
  /\ P_DeliveryFail \in 0..100
  /\ P_NetworkDelay \in 0..100
  /\ P_LBFail \in 0..100
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

InvPriAllocation ==
  ( \E r \in pending : rprio[r] = 1 )
    => \A r2 \in active : (rprio[r2] = 2 => prioMap[target[r2]] = 2)
  \* 若存在高优(prio=1)请求在等待，则任何低优请求只能占用低优实例（避免抢占高优资源）

InvFallbackBudget ==
  RemoteActiveCount <= FallbackBudget
  \* 跨AZ兜底并行预算：同时运行在“非本地AZ”的请求数量不超过预算

InvBackupCrossAZ ==
  \A x \in inst :
    (BackupMap[x] \in inst) => (azMap[BackupMap[x]] /= azMap[x])
  \* 已上线实例 x 的备份实例(若也已上线)必须位于不同 AZ（多副本容灾配置正确性）

Resolved(r) == (r \notin pending) /\ (r \notin active)

EventualCompletion ==
  \A r \in REQS : <> Resolved(r)
  \* 活性：每个请求最终都会“结束”（成功Complete或达到重试上限不再pending/active）

=============================================================================
