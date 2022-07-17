---- MODULE simple_multiline ----

VARIABLE x

Init == 
    /\ x = [
            existsmultiline |-> 
                \E vi \in {1,2}, 
                   vj \in {3,4},
                   vk \in {5,6} : 
                   vi = 0 /\ vj = 2 /\ vk = 6,
            setinmultiline |-> 
                2 \in
                    {1,2,3}, 
            bottom |-> FALSE
        ]  

Next == x' = x

====