---- MODULE AmazonUtils ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* UTILITY LIBRARY                                                         *)
(* Recursive functions fixed for TLC compatibility.                        *)
(***************************************************************************)

(* Find the minimum value in a set of numbers *)
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(* Check if a set is empty *)
IsEmpty(S) == Cardinality(S) = 0

(* Standard TLA+ Recursive Summation *)
RECURSIVE SumSet(_, _)

SumSet(F(_), S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  F(x) + SumSet(F, S \ {x})

Sum(F(_), S) == SumSet(F, S)

(* Filter a set based on a predicate P *)
Filter(S, P(_)) == {x \in S : P(x)}

=============================================================================
