----------------------- MODULE simple_set_of_fns ------------------------
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = [ a |-> [0..1 -> BOOLEAN], 
               b |-> [0..2 -> {"a","b","c"}],
               c |-> [{3,1,2} -> {"q","x","a"}],
               d |-> [[{4,6} -> {2,3}] -> {"y","z"}]]
====