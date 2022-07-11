-------------------------------- MODULE lift --------------------------------
EXTENDS TLC, Integers

CONSTANTS Storeys

ASSUME Storeys \subseteq Int

VARIABLES 
    \* Current location of the car
    carLocation, 
    \* Car’s potential movement states as “idle”, “going up” or “going down”, 
    \* which we will represent numerically as 
    \* 0 for idle, 1 for going up and -1 for going down. 
    carTravelStatus, 
    \* Button on the Storey to call the lift
    callRequest, 
    \* Button inside of lift to go to another Storey
    goRequest

ConstStoreysRange == 1..2

ECInit ==
    /\ carLocation \in Storeys
    /\ carTravelStatus = 0
    /\ callRequest = [s \in Storeys |-> 0]
    /\ goRequest = 0

ECNextCall(s) ==
    /\ callRequest[s] = 0
    /\ callRequest' = [callRequest EXCEPT ![s] = 1]
    /\ UNCHANGED << carLocation, carTravelStatus, goRequest >>

ECNextServiceCall(s) ==
    /\ carLocation # s
    /\ carTravelStatus = 0 
    /\ carTravelStatus' = IF s > carLocation THEN 1 ELSE -1
    /\ UNCHANGED << callRequest, goRequest, carLocation >>

ECNextArriveCall(s) ==
    /\ carLocation # s
    /\ carTravelStatus # 0
    /\ callRequest[s] = 1
    /\ carLocation' = s
    /\ carTravelStatus' = 0
    /\ callRequest' = [callRequest EXCEPT ![s] = 0]
    /\ UNCHANGED << goRequest >>

ECNextGoRequest ==
    /\ goRequest = 0
    /\ goRequest' = 1
    /\ UNCHANGED << carTravelStatus, carLocation, callRequest >>

ECNextServiceGoRequest ==
    /\ goRequest = 1
    /\ carTravelStatus = 0
    /\ carTravelStatus' = IF carLocation = 1 THEN 1 ELSE -1
    /\ UNCHANGED << goRequest, carLocation, callRequest >>


ECNextArriveGoRequest ==
    /\ carTravelStatus # 0
    /\ goRequest = 1
    /\ carLocation' = IF carLocation = 1 THEN 2 ELSE 1
    /\ carTravelStatus' = 0
    /\ goRequest' = 0
    /\ UNCHANGED << callRequest >>

ECNext ==
    \/ \E s \in Storeys :
        \/ ECNextCall(s)
        \/ ECNextServiceCall(s)
        \/ ECNextArriveCall(s)
    \/ ECNextGoRequest
    \/ ECNextServiceGoRequest
    \/ ECNextArriveGoRequest

vars == << carLocation, carTravelStatus, callRequest, goRequest >>

Spec == ECInit /\ [][ECNext]_vars    

(* Invariants
All of the things that should remain true in all states of our system.
*)
ECTypeOK ==
    /\ carLocation \in Storeys
    /\ carTravelStatus \in {-1, 0, 1}
    /\ callRequest \in [Storeys -> {0, 1}]
    /\ goRequest \in {0, 1}

=============================================================================