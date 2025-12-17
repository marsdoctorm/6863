---- MODULE AmazonV3TraceBad ----
(*
  Bad trace:
  - Unhealthy 后未及时 Sync，导致 stale dataPool 仍包含不健康实例
  - 高优请求 r2 被错误地调度到不健康实例 i1，从而触发 InvNoBadRoute
*)

Trace == <<
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
=============================================================================
