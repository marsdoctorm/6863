---- MODULE AmazonLBLogic ----
EXTENDS AmazonConstants, AmazonUtils

(***************************************************************************)
(     *)
(***************************************************************************)

(* Helper: Get the other AZ *)
RemoteAZ(currentAZ) == IF currentAZ = "A" THEN "B" ELSE "A"

(* Filter: Get all ELIGIBLE instances *)
(* CHECKS: 1. AZ Match  2. Status=Ready  3. Capacity  4. Circuit Breaker *)
CandidatesInAZ(pool, azMap, targetAZ, cbMap, loadMap, statusMap, capMap) ==
    { n \in pool :
        /\ azMap[n] = targetAZ
        /\ statusMap[n] = "Ready"
        /\ loadMap[n] < capMap[n]
        /\ \/ cbMap[n] = "Closed"
           \/ (cbMap[n] = "HalfOpen" /\ loadMap[n] = 0)
    }

(* Strategy: Least Connections *)
PickLeastConnections(candidates, loadMap) ==
    IF IsEmpty(candidates) THEN NoInstance
    ELSE CHOOSE x \in candidates :
            \A y \in candidates : loadMap[x] <= loadMap[y]

(* Main Routing Function *)
ComputeRoute(reqOrigin, pool, azMap, cbMap, loadMap, statusMap, capMap) ==
    LET localCands  == CandidatesInAZ(pool, azMap, reqOrigin, cbMap, loadMap, statusMap, capMap)
        remoteCands == CandidatesInAZ(pool, azMap, RemoteAZ(reqOrigin), cbMap, loadMap, statusMap, capMap)
    IN
    IF \neg IsEmpty(localCands)
    THEN PickLeastConnections(localCands, loadMap)
    ELSE
        IF \neg IsEmpty(remoteCands)
        THEN PickLeastConnections(remoteCands, loadMap)
        ELSE NoInstance

=============================================================================

