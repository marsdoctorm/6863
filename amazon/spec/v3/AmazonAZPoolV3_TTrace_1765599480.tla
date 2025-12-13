---- MODULE AmazonAZPoolV3_TTrace_1765599480 ----
EXTENDS AmazonAZPoolV3, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET AmazonAZPoolV3_TEExpression == INSTANCE AmazonAZPoolV3_TEExpression
    IN AmazonAZPoolV3_TEExpression!expression
----

_trace ==
    LET AmazonAZPoolV3_TETrace == INSTANCE AmazonAZPoolV3_TETrace
    IN AmazonAZPoolV3_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        tries = ([r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0])
        /\
        rprio = ([r1 |-> 2, r2 |-> 1, r3 |-> 2, r4 |-> 2])
        /\
        pending = ({})
        /\
        origin = ([r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"])
        /\
        dataPool = ({"i1", "i2", "i3"})
        /\
        active = ({"r2"})
        /\
        i = (17)
        /\
        prioMap = ([i1 |-> 1, i2 |-> 1, i3 |-> 2])
        /\
        azMap = ([i1 |-> "A", i2 |-> "B", i3 |-> "A"])
        /\
        target = ([r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"])
        /\
        capMap = ([i1 |-> 1, i2 |-> 2, i3 |-> 1])
        /\
        blocked = ({"i1"})
        /\
        load = ([i1 |-> 1, i2 |-> 0, i3 |-> 0])
        /\
        healthy = ({"i2", "i3"})
        /\
        inst = ({"i1", "i2", "i3"})
        /\
        controlPool = ({"i1", "i2", "i3"})
        /\
        errors = (0)
    )
----

_init ==
    /\ pending = _TETrace[1].pending
    /\ tries = _TETrace[1].tries
    /\ blocked = _TETrace[1].blocked
    /\ origin = _TETrace[1].origin
    /\ errors = _TETrace[1].errors
    /\ healthy = _TETrace[1].healthy
    /\ target = _TETrace[1].target
    /\ active = _TETrace[1].active
    /\ i = _TETrace[1].i
    /\ capMap = _TETrace[1].capMap
    /\ rprio = _TETrace[1].rprio
    /\ dataPool = _TETrace[1].dataPool
    /\ prioMap = _TETrace[1].prioMap
    /\ azMap = _TETrace[1].azMap
    /\ controlPool = _TETrace[1].controlPool
    /\ load = _TETrace[1].load
    /\ inst = _TETrace[1].inst
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ pending  = _TETrace[i].pending
        /\ pending' = _TETrace[j].pending
        /\ tries  = _TETrace[i].tries
        /\ tries' = _TETrace[j].tries
        /\ blocked  = _TETrace[i].blocked
        /\ blocked' = _TETrace[j].blocked
        /\ origin  = _TETrace[i].origin
        /\ origin' = _TETrace[j].origin
        /\ errors  = _TETrace[i].errors
        /\ errors' = _TETrace[j].errors
        /\ healthy  = _TETrace[i].healthy
        /\ healthy' = _TETrace[j].healthy
        /\ target  = _TETrace[i].target
        /\ target' = _TETrace[j].target
        /\ active  = _TETrace[i].active
        /\ active' = _TETrace[j].active
        /\ i  = _TETrace[i].i
        /\ i' = _TETrace[j].i
        /\ capMap  = _TETrace[i].capMap
        /\ capMap' = _TETrace[j].capMap
        /\ rprio  = _TETrace[i].rprio
        /\ rprio' = _TETrace[j].rprio
        /\ dataPool  = _TETrace[i].dataPool
        /\ dataPool' = _TETrace[j].dataPool
        /\ prioMap  = _TETrace[i].prioMap
        /\ prioMap' = _TETrace[j].prioMap
        /\ azMap  = _TETrace[i].azMap
        /\ azMap' = _TETrace[j].azMap
        /\ controlPool  = _TETrace[i].controlPool
        /\ controlPool' = _TETrace[j].controlPool
        /\ load  = _TETrace[i].load
        /\ load' = _TETrace[j].load
        /\ inst  = _TETrace[i].inst
        /\ inst' = _TETrace[j].inst

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("AmazonAZPoolV3_TTrace_1765599480.json", _TETrace)

=============================================================================

 Note that you can extract this module `AmazonAZPoolV3_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `AmazonAZPoolV3_TEExpression.tla` file takes precedence 
  over the module `AmazonAZPoolV3_TEExpression` below).

---- MODULE AmazonAZPoolV3_TEExpression ----
EXTENDS AmazonAZPoolV3, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `AmazonAZPoolV3` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        pending |-> pending
        ,tries |-> tries
        ,blocked |-> blocked
        ,origin |-> origin
        ,errors |-> errors
        ,healthy |-> healthy
        ,target |-> target
        ,active |-> active
        ,i |-> i
        ,capMap |-> capMap
        ,rprio |-> rprio
        ,dataPool |-> dataPool
        ,prioMap |-> prioMap
        ,azMap |-> azMap
        ,controlPool |-> controlPool
        ,load |-> load
        ,inst |-> inst
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_pendingUnchanged |-> pending = pending'
        
        \* Format the `pending` variable as Json value.
        \* ,_pendingJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(pending)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_pendingModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].pending # _TETrace[s-1].pending
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE AmazonAZPoolV3_TETrace ----
\*EXTENDS AmazonAZPoolV3, IOUtils, TLC
\*
\*trace == IODeserialize("AmazonAZPoolV3_TTrace_1765599480.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE AmazonAZPoolV3_TETrace ----
EXTENDS AmazonAZPoolV3, TLC

trace == 
    <<
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 1,prioMap |-> [i1 |-> 2, i2 |-> 2, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "A", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {},inst |-> {},controlPool |-> {},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 2,prioMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "A", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {},inst |-> {"i1"},controlPool |-> {},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 3,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {},inst |-> {"i1", "i2"},controlPool |-> {},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 4,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {},inst |-> {"i1", "i2", "i3"},controlPool |-> {},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 5,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1"},inst |-> {"i1", "i2", "i3"},controlPool |-> {},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 6,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2"},inst |-> {"i1", "i2", "i3"},controlPool |-> {},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 7,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 8,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 9,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {},active |-> {},i |-> 10,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2", "i3"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {"i1", "i2", "i3"},active |-> {},i |-> 11,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2", "i3"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {"r1"},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {"i1", "i2", "i3"},active |-> {},i |-> 12,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2", "i3"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {"i1", "i2", "i3"},active |-> {"r1"},i |-> 13,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 1, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2", "i3"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {"i1", "i2", "i3"},active |-> {},i |-> 14,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i1", "i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2", "i3"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 2, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {"i1", "i2", "i3"},active |-> {},i |-> 15,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {"i1"},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2", "i3"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 1, r3 |-> 2, r4 |-> 2],pending |-> {"r2"},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {"i1", "i2", "i3"},active |-> {},i |-> 16,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {"i1"},load |-> [i1 |-> 0, i2 |-> 0, i3 |-> 0],healthy |-> {"i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2", "i3"},errors |-> 0]),
    ([tries |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0, r4 |-> 0],rprio |-> [r1 |-> 2, r2 |-> 1, r3 |-> 2, r4 |-> 2],pending |-> {},origin |-> [r1 |-> "A", r2 |-> "A", r3 |-> "A", r4 |-> "A"],dataPool |-> {"i1", "i2", "i3"},active |-> {"r2"},i |-> 17,prioMap |-> [i1 |-> 1, i2 |-> 1, i3 |-> 2],azMap |-> [i1 |-> "A", i2 |-> "B", i3 |-> "A"],target |-> [r1 |-> "i1", r2 |-> "i1", r3 |-> "i1", r4 |-> "i1"],capMap |-> [i1 |-> 1, i2 |-> 2, i3 |-> 1],blocked |-> {"i1"},load |-> [i1 |-> 1, i2 |-> 0, i3 |-> 0],healthy |-> {"i2", "i3"},inst |-> {"i1", "i2", "i3"},controlPool |-> {"i1", "i2", "i3"},errors |-> 0])
    >>
----


=============================================================================

---- CONFIG AmazonAZPoolV3_TTrace_1765599480 ----
CONSTANTS
    UseBad = TRUE
    RetryLimit = 3

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
\* Generated on Fri Dec 12 23:18:01 EST 2025