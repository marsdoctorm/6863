---- MODULE AmazonTraceValidator_TTrace_1765557972 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, AmazonTraceValidator

_expression ==
    LET AmazonTraceValidator_TEExpression == INSTANCE AmazonTraceValidator_TEExpression
    IN AmazonTraceValidator_TEExpression!expression
----

_trace ==
    LET AmazonTraceValidator_TETrace == INSTANCE AmazonTraceValidator_TETrace
    IN AmazonTraceValidator_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        blocked = ({"i1"})
        /\
        healthy = ({})
        /\
        inst = ({"i1"})
        /\
        pool = ({"i1"})
        /\
        i = (6)
    )
----

_init ==
    /\ pool = _TETrace[1].pool
    /\ blocked = _TETrace[1].blocked
    /\ healthy = _TETrace[1].healthy
    /\ i = _TETrace[1].i
    /\ inst = _TETrace[1].inst
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ pool  = _TETrace[i].pool
        /\ pool' = _TETrace[j].pool
        /\ blocked  = _TETrace[i].blocked
        /\ blocked' = _TETrace[j].blocked
        /\ healthy  = _TETrace[i].healthy
        /\ healthy' = _TETrace[j].healthy
        /\ i  = _TETrace[i].i
        /\ i' = _TETrace[j].i
        /\ inst  = _TETrace[i].inst
        /\ inst' = _TETrace[j].inst

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("AmazonTraceValidator_TTrace_1765557972.json", _TETrace)

=============================================================================

 Note that you can extract this module `AmazonTraceValidator_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `AmazonTraceValidator_TEExpression.tla` file takes precedence 
  over the module `AmazonTraceValidator_TEExpression` below).

---- MODULE AmazonTraceValidator_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, AmazonTraceValidator

expression == 
    [
        \* To hide variables of the `AmazonTraceValidator` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        pool |-> pool
        ,blocked |-> blocked
        ,healthy |-> healthy
        ,i |-> i
        ,inst |-> inst
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_poolUnchanged |-> pool = pool'
        
        \* Format the `pool` variable as Json value.
        \* ,_poolJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(pool)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_poolModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].pool # _TETrace[s-1].pool
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE AmazonTraceValidator_TETrace ----
\*EXTENDS IOUtils, TLC, AmazonTraceValidator
\*
\*trace == IODeserialize("AmazonTraceValidator_TTrace_1765557972.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE AmazonTraceValidator_TETrace ----
EXTENDS TLC, AmazonTraceValidator

trace == 
    <<
    ([blocked |-> {},healthy |-> {},inst |-> {},pool |-> {},i |-> 1]),
    ([blocked |-> {},healthy |-> {},inst |-> {"i1"},pool |-> {},i |-> 2]),
    ([blocked |-> {},healthy |-> {"i1"},inst |-> {"i1"},pool |-> {},i |-> 3]),
    ([blocked |-> {},healthy |-> {"i1"},inst |-> {"i1"},pool |-> {"i1"},i |-> 4]),
    ([blocked |-> {"i1"},healthy |-> {},inst |-> {"i1"},pool |-> {},i |-> 5]),
    ([blocked |-> {"i1"},healthy |-> {},inst |-> {"i1"},pool |-> {"i1"},i |-> 6])
    >>
----


=============================================================================

---- CONFIG AmazonTraceValidator_TTrace_1765557972 ----
CONSTANTS
    UseBad = TRUE

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Fri Dec 12 11:46:12 EST 2025