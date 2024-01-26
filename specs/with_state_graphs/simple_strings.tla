----------------------- MODULE simple_strings ------------------------
EXTENDS Sequences,TLC, Naturals
VARIABLE x

Init == 
    \* Certain sequence ops also work for strings.
    \/ x = "a" \o "b"
    \/ x = "dklksj" \o "pty" \o "kkgkg"
    \/ x = Len("abc") + Len("ghjfks")
    
Next == x' = x
====