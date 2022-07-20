---- MODULE simple_unchanged_no_tuple ----

VARIABLE x

Init == x = 0

Next == UNCHANGED x

====