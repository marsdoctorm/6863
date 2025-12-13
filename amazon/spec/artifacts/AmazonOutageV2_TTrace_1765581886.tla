---- MODULE AmazonOutageV2_TTrace_1765581886 ----
EXTENDS Sequences, TLCExt, AmazonOutageV2, Toolbox, Naturals, TLC

_expression ==
    LET AmazonOutageV2_TEExpression == INSTANCE AmazonOutageV2_TEExpression
    IN AmazonOutageV2_TEExpression!expression
----

_trace ==
    LET AmazonOutageV2_TETrace == INSTANCE AmazonOutageV2_TETrace
    IN AmazonOutageV2_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        blocked = ({"i1"})
        /\
        healthy = ({"i2"})
        /\
        dataPool = ({"i1", "i2"})
        /\
        inst = ({"i1", "i2"})
        /\
        azB = ({"i2"})
        /\
        controlPool = ({"i1", "i2"})
        /\
        azA = ({"i1"})
        /\
        i = (13)
        /\
        errors = (1)
    )
----

_init ==
    /\ azA = _TETrace[1].azA
    /\ blocked = _TETrace[1].blocked
    /\ azB = _TETrace[1].azB
    /\ errors = _TETrace[1].errors
    /\ healthy = _TETrace[1].healthy
    /\ i = _TETrace[1].i
    /\ dataPool = _TETrace[1].dataPool
    /\ controlPool = _TETrace[1].controlPool
    /\ inst = _TETrace[1].inst
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ azA  = _TETrace[i].azA
        /\ azA' = _TETrace[j].azA
        /\ blocked  = _TETrace[i].blocked
        /\ blocked' = _TETrace[j].blocked
        /\ azB  = _TETrace[i].azB
        /\ azB' = _TETrace[j].azB
        /\ errors  = _TETrace[i].errors
        /\ errors' = _TETrace[j].errors
        /\ healthy  = _TETrace[i].healthy
        /\ healthy' = _TETrace[j].healthy
        /\ i  = _TETrace[i].i
        /\ i' = _TETrace[j].i
        /\ dataPool  = _TETrace[i].dataPool
        /\ dataPool' = _TETrace[j].dataPool
        /\ controlPool  = _TETrace[i].controlPool
        /\ controlPool' = _TETrace[j].controlPool
        /\ inst  = _TETrace[i].inst
        /\ inst' = _TETrace[j].inst

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("AmazonOutageV2_TTrace_1765581886.json", _TETrace)

=============================================================================

 Note that you can extract this module `AmazonOutageV2_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `AmazonOutageV2_TEExpression.tla` file takes precedence 
  over the module `AmazonOutageV2_TEExpression` below).

---- MODULE AmazonOutageV2_TEExpression ----
EXTENDS Sequences, TLCExt, AmazonOutageV2, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `AmazonOutageV2` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        azA |-> azA
        ,blocked |-> blocked
        ,azB |-> azB
        ,errors |-> errors
        ,healthy |-> healthy
        ,i |-> i
        ,dataPool |-> dataPool
        ,controlPool |-> controlPool
        ,inst |-> inst
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_azAUnchanged |-> azA = azA'
        
        \* Format the `azA` variable as Json value.
        \* ,_azAJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(azA)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_azAModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].azA # _TETrace[s-1].azA
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE AmazonOutageV2_TETrace ----
\*EXTENDS IOUtils, AmazonOutageV2, TLC
\*
\*trace == IODeserialize("AmazonOutageV2_TTrace_1765581886.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE AmazonOutageV2_TETrace ----
EXTENDS AmazonOutageV2, TLC

trace == 
    <<
    ([blocked |-> {},healthy |-> {},dataPool |-> {},inst |-> {},azB |-> {},controlPool |-> {},azA |-> {},i |-> 1,errors |-> 0]),
    ([blocked |-> {},healthy |-> {},dataPool |-> {},inst |-> {"i1"},azB |-> {},controlPool |-> {},azA |-> {"i1"},i |-> 2,errors |-> 0]),
    ([blocked |-> {},healthy |-> {},dataPool |-> {},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {},azA |-> {"i1"},i |-> 3,errors |-> 0]),
    ([blocked |-> {},healthy |-> {"i1"},dataPool |-> {},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {},azA |-> {"i1"},i |-> 4,errors |-> 0]),
    ([blocked |-> {},healthy |-> {"i1", "i2"},dataPool |-> {},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {},azA |-> {"i1"},i |-> 5,errors |-> 0]),
    ([blocked |-> {},healthy |-> {"i1", "i2"},dataPool |-> {},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {"i1"},azA |-> {"i1"},i |-> 6,errors |-> 0]),
    ([blocked |-> {},healthy |-> {"i1", "i2"},dataPool |-> {},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {"i1", "i2"},azA |-> {"i1"},i |-> 7,errors |-> 0]),
    ([blocked |-> {},healthy |-> {"i1", "i2"},dataPool |-> {"i1", "i2"},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {"i1", "i2"},azA |-> {"i1"},i |-> 8,errors |-> 0]),
    ([blocked |-> {},healthy |-> {"i1", "i2"},dataPool |-> {"i1", "i2"},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {"i1", "i2"},azA |-> {"i1"},i |-> 9,errors |-> 0]),
    ([blocked |-> {"i1"},healthy |-> {"i2"},dataPool |-> {"i1", "i2"},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {"i1", "i2"},azA |-> {"i1"},i |-> 10,errors |-> 0]),
    ([blocked |-> {"i1"},healthy |-> {"i2"},dataPool |-> {"i1", "i2"},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {"i1", "i2"},azA |-> {"i1"},i |-> 11,errors |-> 0]),
    ([blocked |-> {"i1"},healthy |-> {"i2"},dataPool |-> {"i1", "i2"},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {"i1", "i2"},azA |-> {"i1"},i |-> 12,errors |-> 0]),
    ([blocked |-> {"i1"},healthy |-> {"i2"},dataPool |-> {"i1", "i2"},inst |-> {"i1", "i2"},azB |-> {"i2"},controlPool |-> {"i1", "i2"},azA |-> {"i1"},i |-> 13,errors |-> 1])
    >>
----


=============================================================================

---- CONFIG AmazonOutageV2_TTrace_1765581886 ----
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
\* Generated on Fri Dec 12 18:24:46 EST 2025