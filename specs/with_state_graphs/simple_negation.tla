---- MODULE simple_negation ----

\* See https://github.com/will62794/tla-web/issues/12.

VARIABLE x

Init == x = TRUE

Next == x' = ~x
====