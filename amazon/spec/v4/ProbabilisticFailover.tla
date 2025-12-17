---- MODULE ProbabilisticFailover ----
EXTENDS Naturals

(***************************************************************************)
(* 概率视角的“文档化”模块                                                 *)
(* 说明：TLA+ / TLC 在模型检查时不会按概率抽样，而是探索所有分支。         *)
(* 因此我们用 0..100 的百分比常量做“语义标注”，并用非确定性分支来建模。  *)
(***************************************************************************)

CONSTANTS P_DeliveryFail, P_NetworkDelay, P_LBFail

ProbParamsOK ==
  /\ P_DeliveryFail \in 0..100
  /\ P_NetworkDelay \in 0..100
  /\ P_LBFail       \in 0..100

(***************************************************************************)
(* 非确定性“结果集”：TLC 会同时探索 TRUE/FALSE 分支。                       *)
(* 你可以把 “TRUE 分支” 理解为“发生故障/延迟/路由失败”，其现实概率分别为： *)
(*   P_DeliveryFail%、P_NetworkDelay%、P_LBFail%                             *)
(***************************************************************************)

Outcome == {TRUE, FALSE}

IsDeliveryFail == TRUE \in Outcome
IsNetworkDelay == TRUE \in Outcome
IsLBFail        == TRUE \in Outcome

=============================================================================
