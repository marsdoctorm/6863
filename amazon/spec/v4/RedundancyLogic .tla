---- MODULE RedundancyLogic ----
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* 地域冗余/备份映射的可复用约束模块                                        *)
(* 说明：把备份关系抽象成 BackupMap，并提供跨AZ一致性约束与预算约束的模板。 *)
(***************************************************************************)

CONSTANTS INSTS, AZS

(*
  BackupMap: 主实例 -> 备份实例
  约定：备份实例最好在不同 AZ（但只有当两边都“已上线/可用”时才强约束）。
*)
BackupCrossAZ(launched, azMap, BackupMap) ==
  \A x \in launched :
    (BackupMap[x] \in launched) => (azMap[BackupMap[x]] /= azMap[x])

(*
  Cross-AZ 并行预算模板：activeRequests 是正在执行的请求集合；
  targetAZ 是请求 -> AZ 的函数；originAZ 是请求 -> AZ 的函数。
*)
FallbackBudgetOK(activeRequests, targetAZ, originAZ, budget) ==
  Cardinality({ r \in activeRequests : targetAZ[r] /= originAZ[r] }) <= budget

=============================================================================
