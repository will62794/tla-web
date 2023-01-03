------------------------------------- MODULE Elevator_anim -------------------------------------
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

EXTENDS     Integers,TLC,FiniteSets,Sequences

Person == {"p1"}
Elevator == {"e1", "e2"}
FloorCount == 3

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



----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Animation and View Definitions for Elevator system                                             *)
(**************************************************************************************************)

\* EXTENDS Elevator, SVG

ToStr(v) == v

Merge(r1, r2) == 
    (**************************************************************************)
    (* Merge two records.                                                     *)
    (*                                                                        *)
    (* If a field appears in both records, then the value from 'r1' is kept.  *)
    (**************************************************************************)
    LET D1 == DOMAIN r1 
        D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) == 
    (**************************************************************************)
    (* SVG element constructor.                                               *)
    (*                                                                        *)
    (* An SVG element like:                                                   *)
    (*                                                                        *)
    (* [name |-> "elem", attrs |-> [k1 |-> "0", k2 |-> "1"], children |->     *)
    (* <<>>, innerText |-> ""]                                                *)
    (*                                                                        *)
    (* would represent the SVG element '<elem k1="0" k2="1"></elem>'          *)
    (**************************************************************************)
    [name       |-> _name, 
     attrs      |-> _attrs, 
     children   |-> _children,
     innerText  |-> _innerText ]

Line(x1, y1, x2, y2, attrs) == 
    (**************************************************************************)
    (* Line element.  'x1', 'y1', 'x2', and 'y2' should be given as integers. *)
    (**************************************************************************)
    LET svgAttrs == [x1 |-> ToStr(x1), 
                     y1 |-> ToStr(y1), 
                     x2 |-> ToStr(x2),
                     y2 |-> ToStr(y2)] IN
    SVGElem("line", Merge(svgAttrs, attrs), <<>>, "")

Circle(cx, cy, r, attrs) == 
    (**************************************************************************)
    (* Circle element. 'cx', 'cy', and 'r' should be given as integers.       *)
    (**************************************************************************)
    LET svgAttrs == [cx |-> ToStr(cx), 
                     cy |-> ToStr(cy), 
                     r  |-> ToStr(r)] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")

Rect(x, y, w, h, attrs) == 
    (**************************************************************************)
    (* Rectangle element.  'x', 'y', 'w', and 'h' should be given as          *)
    (* integers.                                                              *)
    (**************************************************************************)
    LET svgAttrs == [x      |-> ToStr(x), 
                     y      |-> ToStr(y), 
                     width  |-> ToStr(w), 
                     height |-> ToStr(h)] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Text(x, y, text, attrs) == 
    (**************************************************************************)
    (* Text element.'x' and 'y' should be given as integers, and 'text' given *)
    (* as a string.                                                           *)
    (**************************************************************************)
    LET svgAttrs == [x |-> ToStr(x), 
                     y |-> ToStr(y)] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

Group(children, attrs) == 
    (**************************************************************************)
    (* Group element.  'children' is a sequence of elements that will be      *)
    (* contained in this group.                                               *)
    (**************************************************************************)
    SVGElem("g", attrs, children, "")

Svg(children, attrs) == 
    (**************************************************************************)
    (* Svg container.  'children' is a sequence of elements that will be      *)
    (* contained in this svg container.                                       *)
    (**************************************************************************)
    SVGElem("svg", attrs, children, "")

SVGElemToStr(elem) == 
    (**************************************************************************)
    (* Convert an SVG element record into its string representation.          *)
    (*                                                                        *)
    (* This operator is expected to be replaced by a Java module override.    *)
    (* We do not implement it in pure TLA+ because doing non-trivial string   *)
    (* manipulation in TLA+ is tedious.  Also, the performance of             *)
    (* implementing this in TLA+ has been demonstrated to be prohibitively    *)
    (* slow.                                                                  *)
    (**************************************************************************)
    TRUE

-------------------------------------------------------------------------------

(* View helpers. *)
Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

SetToSeq(S) == 
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)

\* Establish a fixed mapping to assign an ordering to elements in these sets.
PersonId == CHOOSE f \in [Person -> 1..Cardinality(Person)] : Injective(f)
ElevatorId == CHOOSE f \in [Elevator -> 1..Cardinality(Elevator)] : Injective(f)

\* Dimensions of an elevator.
ElevatorDims == [width |-> 35, height |-> 50]
FloorHeight == ElevatorDims.height + 10
FloorYPos(f) == f * FloorHeight

\* Gives the (x,y) base position of an elevator.
ElevatorPos(e) ==  [x |-> (150 + ElevatorId[e] * (ElevatorDims.width + 3)), y |-> FloorYPos(ElevatorState[e].floor)]
    
(**************************************************************************************************)
(* ELEVATOR elements.                                                                             *)
(**************************************************************************************************)
ElevatorElem(e) ==  
    LET pos == ElevatorPos(e)
        dims == ElevatorDims 
        color == IF ElevatorState[e].doorsOpen THEN "green" ELSE "black" IN
    Rect(pos.x, pos.y, dims.width, dims.height, [fill |-> color])   

\* Elements that show which direction an elevator is moving.
ElevatorDirElem(e) == 
    LET pos == ElevatorPos(e)
        dims == ElevatorDims 
        mid == pos.y + 17
        yPos == IF ElevatorState[e].direction = "Down" 
                    THEN mid - 17
                    ELSE IF ElevatorState[e].direction = "Up" THEN mid + 17
                    ELSE mid IN
    Rect(pos.x + 1, yPos, dims.width-2, 2, [fill |-> "white"])     

ElevatorDirElems == {ElevatorDirElem(e) : e \in Elevator}
ElevatorElems == {ElevatorElem(e) : e \in Elevator}

(**************************************************************************************************)
(* PERSON Elements.                                                                               *)
(**************************************************************************************************) 

PersonRadius == 3
PersonXPosBase == 30
PersonXPos(xBase, p) == xBase + (PersonId[p] * 9)
PersonYPos(p) == FloorYPos(PersonState[p].location) + 10

\* Person who is currently on a floor, not in an elevator.
FloorPersonElem(p) == 
    LET person == PersonState[p]
        pos == [y |-> PersonYPos(p), x |-> PersonXPos(PersonXPosBase, p)]
        color == IF person.waiting THEN "darkred" ELSE "blue" IN
        Circle(pos.x, pos.y, PersonRadius, [fill |-> color])

\* Person who is currently in an elevator.
ElevatorPersonElem(p) == 
    LET person == PersonState[p]
        elevPos == ElevatorPos(person.location) 
        pos == [elevPos EXCEPT !.x = PersonXPos(elevPos.x, p), !.y = @ + 10] IN
        Circle(pos.x, pos.y, PersonRadius, [fill |-> "gray"])   

PersonElem(p) == 
    \* A person should always be waiting or in an elevator.
    LET person == PersonState[p] IN
    CASE person.location \in Floor -> FloorPersonElem(p)
      [] person.location \in Elevator -> ElevatorPersonElem(p)
      
PersonDestinationElem(p) ==
    LET person == PersonState[p] IN
    CASE person.location \in Floor -> 
            LET xPos == PersonXPos(PersonXPosBase, p) 
                dims == (IF (person.destination > person.location)
                    THEN [height |-> (FloorYPos(person.destination) - PersonYPos(p)),
                          yPos   |-> PersonYPos(p)]
                    ELSE [height |->  (PersonYPos(p) - FloorYPos(person.destination)),
                          yPos   |->  FloorYPos(person.destination)]) IN
                Rect(xPos, dims.yPos, 1, dims.height, [fill |-> "lightgray"])
      [] person.location \in Elevator -> 
            LET elevator == ElevatorState[person.location]
                elevPos == ElevatorPos(person.location) 
                xPos == PersonXPos(elevPos.x, p) 
                personYPos == elevPos.y + 10
                dims == (IF (person.destination > elevator.floor)
                    THEN [height |-> (FloorYPos(person.destination) - personYPos),
                          yPos   |-> personYPos]
                    ELSE [height |->  (personYPos - FloorYPos(person.destination)),
                          yPos   |->  FloorYPos(person.destination)]) IN
                Rect(xPos, dims.yPos, 1, dims.height, [fill |-> "lightgray"])
          
PersonDestinationElems == {PersonDestinationElem(p) : p \in Person}
PeopleTitle == Text(PersonXPosBase, 50, "People", <<>>)
PersonElems == {PersonElem(p) : p \in Person} \cup PersonDestinationElems

(**************************************************************************************************)
(* ELEVATOR CALL elements.                                                                        *)
(**************************************************************************************************)
IsFloorCall(floor, dir) == \E c \in ActiveElevatorCalls : c.floor = floor /\ c.direction = dir

ButtonXPos == 90
Button(floor, dir) == 
    LET x == ButtonXPos
        y == FloorYPos(floor) + (IF dir = "Up" THEN 25 ELSE 16) IN
        Rect(x, y, 7, 7, [fill |-> IF IsFloorCall(floor, dir) THEN "orange" ELSE "black"])

ElevatorButtonElem(floor) ==
    LET upButton == Button(floor, "Up")
        downButton ==  Button(floor, "Down") IN
        Group(<<upButton, downButton>>, <<>>)

ElevatorButtonElems == {ElevatorButtonElem(f) : f \in Floor}

(**************************************************************************************************)
(* FLOOR elements.                                                                                *)
(**************************************************************************************************)

FloorSeparator(floor) == Rect(5, FloorYPos(floor), 350, 1, [fill |-> "lightgray"])
FloorSeparators == {FloorSeparator(f) : f \in Floor}

\* FloorLabel(floor) == Text(10, FloorYPos(floor)+15, ToStr(floor), <<>>)
FloorLabel(floor) == Text(10, FloorYPos(floor)+15, ToStr(floor), <<>>)
FloorLabels == {FloorLabel(f) : f \in Floor}

AllElems == SetToSeq(ElevatorElems) \o
            SetToSeq(FloorSeparators) \o
            SetToSeq(FloorLabels) \o
            SetToSeq(ElevatorDirElems) \o
            SetToSeq(PersonElems) \o
            \* <<PeopleTitle>> \o
            \* SetToSeq(ElevatorButtonElems) \o
            <<>>

\* Overall animation view.
\* View == Group(AllElems, ("color" :> "black"))
View == Group(AllElems, ("color" :> "black"))

Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y

====================================================================================================