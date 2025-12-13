------------------------- MODULE CloudflareConfig -------------------------
(***************************************************************************)
(* Cloudflare Configuration Propagation Model                              *)
(* This specification models the configuration update process in a         *)
(* distributed edge network similar to Cloudflare's architecture.          *)
(*                                                                         *)
(* Key Components:                                                         *)
(* - Control Plane (CP): Generates and distributes configuration          *)
(* - Data Plane (DP): Edge nodes executing the configuration              *)
(* - Configuration Versions: v1, v2, v3, ...                              *)
(*                                                                         *)
(* Failure Modes Modeled:                                                 *)
(* A) Config valid locally but breaks globally                            *)
(* B) Version skew between CP and DP                                      *)
(* C) Rollback path blocked by new config                                 *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Node,           \* Set of edge nodes (Data Plane)
    ConfigVersion,  \* Set of configuration versions {v1, v2, v3}
    InitConfig,     \* Initial safe configuration
    MaxRollouts     \* Maximum rollout attempts

VARIABLES
    cpState,        \* Control plane state: "idle", "deploying", "rollback", "blocked"
    cpVersion,      \* Current config version in control plane
    nodeConfig,     \* nodeConfig[n] = config version at node n
    nodeState,      \* nodeState[n] = "running", "updating", "failed", "blocked"
    deployedNodes,  \* Set of nodes that received current version
    msgs,           \* Messages in flight: [type, version, dest]
    rolloutCount,   \* Number of rollout attempts
    trafficBlocked  \* Boolean: is traffic being blocked?

vars == <<cpState, cpVersion, nodeConfig, nodeState, deployedNodes, msgs, rolloutCount, trafficBlocked>>

(***************************************************************************)
(* Type Invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ cpState \in {"idle", "deploying", "rollback", "blocked"}
    /\ cpVersion \in ConfigVersion
    /\ nodeConfig \in [Node -> ConfigVersion]
    /\ nodeState \in [Node -> {"running", "updating", "failed", "blocked"}]
    /\ deployedNodes \subseteq Node
    /\ msgs \subseteq [type: {"deploy", "rollback", "ack", "fail"}, 
                       version: ConfigVersion, 
                       node: Node]
    /\ rolloutCount \in 0..MaxRollouts
    /\ trafficBlocked \in BOOLEAN

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)
Init ==
    /\ cpState = "idle"
    /\ cpVersion = InitConfig
    /\ nodeConfig = [n \in Node |-> InitConfig]
    /\ nodeState = [n \in Node |-> "running"]
    /\ deployedNodes = {}
    /\ msgs = {}
    /\ rolloutCount = 0
    /\ trafficBlocked = FALSE

(***************************************************************************)
(* Helper: Check if a configuration combination is valid                  *)
(* Simulates Failure Mode A: certain version combinations break the system*)
(***************************************************************************)
ConfigCombinationValid(configs) ==
    \* Example: if more than 50% nodes have different versions, traffic may be blocked
    \* This simulates version skew causing routing issues
    LET versions == {configs[n] : n \in Node}
        \* If we have 3+ different versions active, system becomes unstable
    IN Cardinality(versions) < 3

(***************************************************************************)
(* Helper: Check if rollback is possible from current state               *)
(* Simulates Failure Mode C: rollback path may be blocked                *)
(***************************************************************************)
RollbackPossible ==
    \* Rollback is blocked if:
    \* 1) Control plane itself is blocked, OR
    \* 2) Current config prevents control plane messages from routing
    /\ cpState # "blocked"
    /\ trafficBlocked = FALSE

(***************************************************************************)
(* Control Plane Actions                                                  *)
(***************************************************************************)

\* CP initiates a new configuration rollout
CPStartRollout(newVersion) ==
    /\ cpState = "idle"
    /\ newVersion \in ConfigVersion
    /\ newVersion # cpVersion
    /\ rolloutCount < MaxRollouts
    /\ cpState' = "deploying"
    /\ cpVersion' = newVersion
    /\ deployedNodes' = {}
    /\ msgs' = msgs \cup {[type |-> "deploy", version |-> newVersion, node |-> n] : n \in Node}
    /\ rolloutCount' = rolloutCount + 1
    /\ UNCHANGED <<nodeConfig, nodeState, trafficBlocked>>

\* CP decides to rollback (manual intervention or automatic)
CPInitiateRollback ==
    /\ cpState = "deploying"
    /\ RollbackPossible
    /\ \E oldVersion \in ConfigVersion :
        /\ oldVersion # cpVersion
        /\ cpState' = "rollback"
        /\ cpVersion' = oldVersion
        /\ msgs' = msgs \cup {[type |-> "rollback", version |-> oldVersion, node |-> n] : n \in Node}
        /\ deployedNodes' = {}
        /\ UNCHANGED <<nodeConfig, nodeState, rolloutCount, trafficBlocked>>

\* CP completes deployment
CPFinishDeployment ==
    /\ cpState = "deploying"
    /\ deployedNodes = Node  \* All nodes deployed
    /\ cpState' = "idle"
    /\ UNCHANGED <<cpVersion, nodeConfig, nodeState, deployedNodes, msgs, rolloutCount, trafficBlocked>>

(***************************************************************************)
(* Data Plane (Node) Actions                                              *)
(***************************************************************************)

\* Node receives and applies configuration
NodeReceiveDeploy(n) ==
    /\ [type |-> "deploy", version |-> cpVersion, node |-> n] \in msgs
    /\ nodeState[n] = "running"
    /\ nodeState' = [nodeState EXCEPT ![n] = "updating"]
    /\ UNCHANGED <<cpState, cpVersion, nodeConfig, deployedNodes, msgs, rolloutCount, trafficBlocked>>

\* Node completes configuration update
NodeCompleteUpdate(n) ==
    /\ nodeState[n] = "updating"
    /\ nodeConfig' = [nodeConfig EXCEPT ![n] = cpVersion]
    /\ nodeState' = [nodeState EXCEPT ![n] = "running"]
    /\ deployedNodes' = deployedNodes \cup {n}
    /\ msgs' = msgs \cup {[type |-> "ack", version |-> cpVersion, node |-> n]}
    \* Check if new configuration combination is valid
    /\ IF ConfigCombinationValid(nodeConfig')
       THEN trafficBlocked' = FALSE
       ELSE trafficBlocked' = TRUE
    /\ UNCHANGED <<cpState, cpVersion, rolloutCount>>

\* Node fails to apply configuration (simulates config that breaks node)
NodeFailUpdate(n) ==
    /\ nodeState[n] = "updating"
    /\ nodeState' = [nodeState EXCEPT ![n] = "failed"]
    /\ msgs' = msgs \cup {[type |-> "fail", version |-> cpVersion, node |-> n]}
    /\ UNCHANGED <<cpState, cpVersion, nodeConfig, deployedNodes, rolloutCount, trafficBlocked>>

\* Node receives rollback command
NodeReceiveRollback(n) ==
    /\ \E msg \in msgs :
        /\ msg.type = "rollback"
        /\ msg.node = n
        /\ nodeConfig' = [nodeConfig EXCEPT ![n] = msg.version]
        /\ nodeState' = [nodeState EXCEPT ![n] = "running"]
        /\ deployedNodes' = deployedNodes \cup {n}
        /\ UNCHANGED <<cpState, cpVersion, msgs, rolloutCount, trafficBlocked>>

(***************************************************************************)
(* System Failures - These represent the Cloudflare incident scenarios    *)
(***************************************************************************)

\* Failure Mode A: Valid config locally, breaks globally
GlobalConfigFailure ==
    /\ ~ConfigCombinationValid(nodeConfig)
    /\ trafficBlocked' = TRUE
    /\ UNCHANGED <<cpState, cpVersion, nodeConfig, nodeState, deployedNodes, msgs, rolloutCount>>

\* Failure Mode B: Control plane becomes blocked due to config issues
ControlPlaneBlocked ==
    /\ trafficBlocked = TRUE
    /\ cpState \in {"deploying", "rollback"}
    /\ cpState' = "blocked"
    /\ UNCHANGED <<cpVersion, nodeConfig, nodeState, deployedNodes, msgs, rolloutCount, trafficBlocked>>

(***************************************************************************)
(* Next State Relation                                                    *)
(***************************************************************************)
Next ==
    \/ \E v \in ConfigVersion : CPStartRollout(v)
    \/ CPInitiateRollback
    \/ CPFinishDeployment
    \/ \E n \in Node :
        \/ NodeReceiveDeploy(n)
        \/ NodeCompleteUpdate(n)
        \/ NodeFailUpdate(n)
        \/ NodeReceiveRollback(n)
    \/ GlobalConfigFailure
    \/ ControlPlaneBlocked

(***************************************************************************)
(* Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Critical Safety Properties (Invariants)                                *)
(***************************************************************************)

\* INVARIANT 1: Traffic should never be blocked indefinitely
TrafficAlwaysAvailable ==
    trafficBlocked = FALSE

\* INVARIANT 2: If traffic is blocked, rollback must be possible
RollbackAvailableWhenBlocked ==
    trafficBlocked => RollbackPossible

\* INVARIANT 3: Control plane should not get stuck
ControlPlaneNotBlocked ==
    cpState # "blocked"

\* INVARIANT 4: All nodes should eventually converge to same version
\* (This is a liveness property, but we can check bounded convergence)
NodesConverging ==
    cpState = "idle" => (deployedNodes = Node)

\* INVARIANT 5: No more than max rollout attempts
RolloutBounded ==
    rolloutCount <= MaxRollouts

(***************************************************************************)
(* Temporal Properties (Liveness - for model checking)                   *)
(***************************************************************************)

\* Eventually, system should return to stable state
EventuallyStable ==
    <>(cpState = "idle" /\ trafficBlocked = FALSE)

\* If rollback is initiated, it should eventually complete
RollbackCompletes ==
    (cpState = "rollback") ~> (cpState = "idle")

=============================================================================
