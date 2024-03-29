------------------------------------- MODULE Elevator -------------------------------------
(***************************************************************************)
(* This spec describes a simple multi-car elevator system. The actions in  *)
(* this spec are unsurprising and common to all such systems except for    *)
(* DispatchElevator, which contains the logic to determine which elevator  *)
(* ought to service which call. The algorithm used is very simple and does *)
(* not optimize for global throughput or average wait time. The            *)
(* TemporalInvariant definition ensures this specification provides        *)
(* capabilities expected of any elevator system, such as people eventually *)
(* reaching their destination floor.                                       *)
(*                                                                         *)
(* Original spec: https://github.com/ahelwer/runway-tla-eval/Elevator.tla  *)                                      
(***************************************************************************)

EXTENDS     Integers,TLC

Person == {"p1"}
Elevator == {"e1"}
FloorCount == 2

VARIABLES   PersonState,            \* The state of each person
            ActiveElevatorCalls,    \* The set of all active elevator calls
            ElevatorState           \* The state of each elevator
         
Vars == \* Tuple of all specification variables
    <<PersonState, ActiveElevatorCalls, ElevatorState>>

Floor ==    \* The set of all floors
    1 .. FloorCount

Direction ==    \* Directions available to this elevator system
    {"Up", "Down"}

ElevatorCall == \* The set of all elevator calls
    [floor : Floor, direction : Direction]

ElevatorDirectionState ==   \* Elevator movement state; it is either moving in a direction or stationary
    Direction \cup {"Stationary"}

GetDistance[f1, f2 \in Floor] ==    \* The distance between two floors
    IF f1 > f2 THEN f1 - f2 ELSE f2 - f1
    
GetDirection[current, destination \in Floor] == \* Direction of travel required to move between current and destination floors
    IF destination > current THEN "Up" ELSE "Down"

CanServiceCall[e \in Elevator, c \in ElevatorCall] ==   \* Whether elevator is in position to immediately service call
    LET eState == ElevatorState[e] IN
    /\ c.floor = eState.floor
    /\ c.direction = eState.direction

PeopleWaiting[f \in Floor, d \in ElevatorDirectionState] ==  \* The set of all people waiting on an elevator call
    {p \in Person :
        /\ PersonState[p].location \notin Floor
        /\ PersonState[p].location = f
        /\ PersonState[p].waiting
        /\ GetDirection[PersonState[p].location, PersonState[p].destination] = d}

PickNewDestination(p) ==    \* Person decides they need to go to a different floor
    LET pState == PersonState[p] IN
    /\ ~pState.waiting
    /\ pState.location \in Floor
    /\ \E f \in Floor :
        /\ f /= pState.location
        /\ PersonState' = [PersonState EXCEPT ![p] = [@ EXCEPT !.destination = f]]
    /\ UNCHANGED <<ActiveElevatorCalls, ElevatorState>>

CallElevator(p) ==  \* Person calls the elevator to go in a certain direction from their floor
    LET pState == PersonState[p] IN
    LET call == [floor |-> pState.location, direction |-> GetDirection[pState.location, pState.destination]] IN
    /\ ~pState.waiting
    /\ pState.location /= pState.destination
    /\ ActiveElevatorCalls' =
        IF \E e \in Elevator :
            /\ CanServiceCall[e, call]
            /\ ElevatorState[e].doorsOpen
        THEN ActiveElevatorCalls
        ELSE ActiveElevatorCalls \cup {call}
    /\ PersonState' = [PersonState EXCEPT ![p] = [@ EXCEPT !.waiting = TRUE]]
    /\ UNCHANGED <<ElevatorState>>

OpenElevatorDoors(e) == \* Open the elevator doors if there is a call on this floor or the button for this floor was pressed.
    LET eState == ElevatorState[e] IN
    /\ ~eState.doorsOpen
    /\  \/ \E call \in ActiveElevatorCalls : CanServiceCall[e, call]
        \/ eState.floor \in eState.buttonsPressed
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.doorsOpen = TRUE, !.buttonsPressed = @ \ {eState.floor}]]
    /\ ActiveElevatorCalls' = ActiveElevatorCalls \ {[floor |-> eState.floor, direction |-> eState.direction]}
    /\ UNCHANGED <<PersonState>>
    
EnterElevator(e) == \* All people on this floor who are waiting for the elevator and travelling the same direction enter the elevator.
    LET eState == ElevatorState[e] IN
    LET gettingOn == PeopleWaiting[eState.floor, eState.direction] IN
    LET destinations == {PersonState[p].destination : p \in gettingOn} IN
    \* /\ PrintT(gettingOn)
    /\ eState.doorsOpen
    /\ eState.direction /= "Stationary"
    /\ gettingOn /= {}
    /\ PersonState' = [p \in Person |->
        IF p \in gettingOn
        THEN [PersonState[p] EXCEPT !.location = e]
        ELSE PersonState[p]]
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.buttonsPressed = @ \cup destinations]]
    /\ UNCHANGED <<ActiveElevatorCalls>>

ExitElevator(e) ==  \* All people whose destination is this floor exit the elevator.
    LET eState == ElevatorState[e] IN
    LET gettingOff == {p \in Person : 
            /\ PersonState[p].location \notin Floor 
            /\ PersonState[p].location = e 
            /\ PersonState[p].destination = eState.floor} IN
    /\ eState.doorsOpen
    /\ gettingOff /= {}
    /\ PersonState' = [p \in Person |->
        IF p \in gettingOff
        THEN [PersonState[p] EXCEPT !.location = eState.floor, !.waiting = FALSE]
        ELSE PersonState[p]]
    /\ UNCHANGED <<ActiveElevatorCalls, ElevatorState>>

CloseElevatorDoors(e) ==    \* Close the elevator doors once all people have entered and exited the elevator on this floor.
    LET eState == ElevatorState[e] IN
    /\ ~ENABLED EnterElevator(e)
    /\ ~ENABLED ExitElevator(e)
    /\ eState.doorsOpen
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.doorsOpen = FALSE]]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

MoveElevator(e) ==  \* Move the elevator to the next floor unless we have to open the doors here.
    LET eState == ElevatorState[e] IN
    LET nextFloor == IF eState.direction = "Up" THEN eState.floor + 1 ELSE eState.floor - 1 IN
    /\ eState.direction /= "Stationary"
    /\ ~eState.doorsOpen
    /\ eState.floor \notin eState.buttonsPressed
    /\ \A call \in ActiveElevatorCalls : \* Can move only if other elevator servicing call
        /\ CanServiceCall[e, call] =>
            /\ \E e2 \in Elevator :
                /\ e /= e2
                /\ CanServiceCall[e2, call]
    /\ nextFloor \in Floor
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.floor = nextFloor]]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

StopElevator(e) == \* Stops the elevator if it's moved as far as it can in one direction
    LET eState == ElevatorState[e] IN
    LET nextFloor == IF eState.direction = "Up" THEN eState.floor + 1 ELSE eState.floor - 1 IN
    /\ ~ENABLED OpenElevatorDoors(e)
    /\ ~eState.doorsOpen
    /\ nextFloor \notin Floor
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.direction = "Stationary"]]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

(***************************************************************************)
(* This action chooses an elevator to service the call. The simple         *)
(* algorithm picks the closest elevator which is either stationary or      *)
(* already moving toward the call floor in the same direction as the call. *)
(* The system keeps no record of assigning an elevator to service a call.  *)
(* It is possible no elevator is able to service a call, but we are        *)
(* guaranteed an elevator will eventually become available.                *)
(***************************************************************************)
DispatchElevator(c) ==
    LET stationary == {e \in Elevator : ElevatorState[e].direction = "Stationary"} IN
    LET approaching == {e \in Elevator :
        /\ ElevatorState[e].direction = c.direction
        /\  \/ ElevatorState[e].floor = c.floor
            \/ GetDirection[ElevatorState[e].floor, c.floor] = c.direction } IN
    /\ c \in ActiveElevatorCalls
    /\ stationary \cup approaching /= {}
    /\ ElevatorState' = 
        LET closest == CHOOSE e \in stationary \cup approaching :
            /\ \A e2 \in stationary \cup approaching :
                /\ GetDistance[ElevatorState[e].floor, c.floor] <= GetDistance[ElevatorState[e2].floor, c.floor] IN
        IF closest \in stationary
        THEN [ElevatorState EXCEPT ![closest] = [@ EXCEPT !.floor = c.floor, !.direction = c.direction]]
        ELSE ElevatorState
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

Init == 
    \* Have people start at a random floor.
    /\ PersonState \in [Person -> [location : Floor, destination : Floor, waiting : {FALSE}]]
    /\ ActiveElevatorCalls = {}
    \* Have all elevators start at the first floor.
    /\ ElevatorState \in [Elevator -> [floor : {1}, direction : {"Stationary"}, doorsOpen : {FALSE}, buttonsPressed : {{}}]]
    
Next == \* The next-state relation
    \/ \E p \in Person : PickNewDestination(p)
    \/ \E p \in Person : CallElevator(p)
    \/ \E e \in Elevator : OpenElevatorDoors(e)
    \/ \E e \in Elevator : EnterElevator(e)
    \/ \E e \in Elevator : ExitElevator(e)
    \/ \E e \in Elevator : CloseElevatorDoors(e)
    \/ \E e \in Elevator : MoveElevator(e)
    \/ \E e \in Elevator : StopElevator(e)
    \/ \E c \in ElevatorCall : DispatchElevator(c)

Spec == 
    /\ Init
    /\ [][Next]_Vars
\*    /\ TemporalAssumptions    

====================================================================================================
\* Modification History
\* Last modified Wed Mar 28 20:46:03 EDT 2018 by williamschultz
\* Created Fri Mar 23 00:50:27 EDT 2018 by williamschultz

\* Modification History
\* Created Sun Mar 25 12:32:39 EDT 2018 by williamschultz