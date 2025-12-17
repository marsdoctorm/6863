---- MODULE AmazonCBLogic ----
EXTENDS AmazonConstants, AmazonUtils

(***************************************************************************)
(* CIRCUIT BREAKER LOGIC MODULE                                            *)
(* Implements the 3-State FSM (Closed -> Open -> HalfOpen).                *)
(***************************************************************************)

(* Determine next state on SUCCESS *)
NextStateOnSuccess(currentState, currentFailCount) ==
    CASE currentState = "HalfOpen" -> "Closed"
      [] currentState = "Open"     -> "Open"
      [] currentState = "Closed"   -> "Closed"
      [] OTHER                     -> currentState

(* Determine next state on FAILURE *)
NextStateOnFail(currentState, currentFailCount) ==
    LET newCount == currentFailCount + 1 IN
    CASE currentState = "HalfOpen" -> "Open"
      [] currentState = "Closed"   ->
            IF newCount >= CircuitThreshold THEN "Open" ELSE "Closed"
      [] currentState = "Open"     -> "Open"
      [] OTHER                     -> currentState

=============================================================================
