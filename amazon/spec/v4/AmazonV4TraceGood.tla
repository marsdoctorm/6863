---- MODULE AmazonV3TraceGood ----
(*
  Good trace (增强版):
  - 原有 good trace：Unhealthy 后立即 Deregister + Sync，避免 stale dataPool
  - 新增 r3：低优请求本地(i3)失败一次 -> 隔离i3并同步 -> 重试跨AZ兜底到i2 完成
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
=============================================================================
