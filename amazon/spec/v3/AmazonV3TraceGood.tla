---- MODULE AmazonV3TraceGood ----
(*
  Good trace: Unhealthy 后立刻 Deregister，并 Sync 刷新 dataPool
  高优先级请求 r2 (prio=1) 在 A 区没有 prio=1 且有容量的实例 -> fallback 到 B 的 i2
*)
Trace ==
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

  [type |-> "Unhealthy", id |-> "i1"],
  [type |-> "Deregister", id |-> "i1"],
  [type |-> "Sync"],

  [type |-> "Req", req |-> "r2", az |-> "A", prio |-> 1],
  [type |-> "Schedule", req |-> "r2"],
  [type |-> "Complete", req |-> "r2"]
>>
=============================================================================
