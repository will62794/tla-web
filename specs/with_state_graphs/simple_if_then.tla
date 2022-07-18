----------------------- MODULE simple_if_then ------------------------
VARIABLE x
Init == x = [
    if1 |-> IF TRUE THEN 1 ELSE 2,
    if2 |-> IF FALSE THEN 1 ELSE IF TRUE THEN 2 ELSE 3
]
Next == x' = x
====