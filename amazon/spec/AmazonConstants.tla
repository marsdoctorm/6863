---- MODULE AmazonConstants ----
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* SYSTEM CONSTANTS & TYPE DEFINITIONS                                     *)
(***************************************************************************)

CONSTANTS
    UseBad,             \* Toggle for fault injection / trace selection
    RetryLimit,         \* Max retries per request
    CircuitThreshold    \* Failure count threshold for CB

(* Physical Constants *)
AZS   == {"A", "B"}
INSTS == {"i1", "i2", "i3"}
REQS  == {"r1", "r2", "r3", "r4"}

(* Type Constraints for Sanity Checking *)
StatusType == {"Offline", "Booting", "Ready", "Down"}
CBStateType == {"Closed", "Open", "HalfOpen"}

(* Helper: Null values for uninitialized states *)
NoInstance == "None"

=============================================================================
