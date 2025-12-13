---- MODULE AmazonTraceGood ----
EXTENDS Sequences
Trace == <<
  [t |-> 0, type |-> "Launch",     id |-> "i1"],
  [t |-> 1, type |-> "Healthy",    id |-> "i1"],
  [t |-> 2, type |-> "Register",   id |-> "i1"],
  [t |-> 3, type |-> "Unhealthy",  id |-> "i1"],
  [t |-> 4, type |-> "Deregister", id |-> "i1"],
  [t |-> 5, type |-> "Terminate",  id |-> "i1"]
>>
====
