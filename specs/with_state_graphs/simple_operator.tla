---- MODULE simple_operator ----
EXTENDS Naturals

VARIABLE x

\* One normal operator def.
Op(u, v) == u + v

Init ==
    \/ x = Op(16, 47)
    
Next ==
    x' = x

====