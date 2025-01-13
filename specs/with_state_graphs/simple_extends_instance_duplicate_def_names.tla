---- MODULE simple_extends_instance_duplicate_def_names ----
EXTENDS Sequences, Naturals

VARIABLES x

A1Inst == INSTANCE A1
A2Inst == INSTANCE A2

Init == x = A1Inst!Val + A2Inst!Val

Next == x' = x

====