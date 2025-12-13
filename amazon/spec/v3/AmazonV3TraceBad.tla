---- MODULE AmazonV3TraceBad ----
(*
  Bad trace: i1 先被标记 Unhealthy，但没有及时 Deregister/Sync
  dataPool 仍包含 i1；高优先级请求 r2 (prio=1) 在 A 区只有 i1 满足 Supports -> 直接路由到坏实例
  => InvNoBadRoute violated
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

  [type |-> "Req", req |-> "r2", az |-> "A", prio |-> 1],
  [type |-> "Schedule", req |-> "r2"]
>>
=============================================================================
