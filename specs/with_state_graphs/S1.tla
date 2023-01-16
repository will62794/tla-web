\* See https://github.com/will62794/tla-web/issues/31.
-------------------------------- MODULE S1 -------------------------------
VARIABLES p

Init == p = FALSE

Next == p' \in BOOLEAN
============================================================================