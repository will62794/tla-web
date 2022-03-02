---- MODULE tla_expr_eval ----
EXTENDS TLC, Naturals

VARIABLE exprs

Init == exprs = [
    add |-> 5 + 5,
    setunion |-> {1,2} \cup {2,3}
]
    
Next == UNCHANGED exprs
====