---- MODULE simple_extends_instance_def_with_var_subst_default_name ----
EXTENDS Sequences, Naturals

VARIABLES x

\* These are both declarations inside M6, so if we define them here,
\* this works since by default, any WITH statements that don't 
\* specify a substitution for a declaration D in M6 will automatically
\* be replaced with D <- D (i.e. the default substitution is the identity).
V == 12
m == x

M == INSTANCE simple_extends_M6

Init == 
    \/ x = 5
    \/ M!MVarInitZero

Next == x' = x

====