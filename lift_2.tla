-------------------------------- MODULE lift_2 --------------------------------
EXTENDS TLC, Integers

CONSTANTS Floors

ASSUME Floors \subseteq Int

VARIABLES 
    \* Current location of the cabin
    cabinLocation, 
    \* Cabin’s potential movement states as “idle”, “going up” or “going down”, 
    \* which we will represent numerically as 
    \* 0 for idle, 1 for going up and -1 for going down. 
    cabinTravelStatus, 
    \* Button on the Floor to call the lift
    callRequest, 
    \* Button inside of lift to go to another Floor
    goRequest

ConstFloorsRange == 1..10

ECInit ==
    /\ cabinLocation \in Floors
    /\ cabinTravelStatus = 0
    /\ callRequest = [f \in Floors |-> 0]
    /\ goRequest = [f \in Floors |-> 0]

ECNextCall(f) ==
    /\ callRequest[f] = 0
    /\ callRequest' = [callRequest EXCEPT ![f] = 1]
    /\ UNCHANGED << cabinLocation, cabinTravelStatus, goRequest >>

ECNextServiceCall(f) ==
    /\ cabinLocation # f
    /\ cabinTravelStatus = 0 
    /\ cabinTravelStatus' = IF f > cabinLocation THEN 1 ELSE -1
    /\ UNCHANGED << callRequest, goRequest, cabinLocation >>

ECNextArriveCall(f) ==
    /\ cabinLocation # f
    /\ cabinTravelStatus # 0
    /\ callRequest[f] = 1
    /\ cabinLocation' = f
    /\ cabinTravelStatus' = 0
    /\ callRequest' = [callRequest EXCEPT ![f] = 0]
    /\ UNCHANGED << goRequest >>

ECNextGoRequest(f) ==
    /\ goRequest[f] = 0
    /\ cabinLocation # f
    /\ goRequest' = [goRequest EXCEPT ![f] = 1]
    /\ UNCHANGED << cabinTravelStatus, cabinLocation, callRequest >>

ECNextServiceGoRequest(f) ==
    /\ goRequest[f] = 1
    /\ cabinLocation # f
    /\ cabinTravelStatus' = IF cabinLocation < f THEN 1 ELSE -1
    /\ UNCHANGED << goRequest, cabinLocation, callRequest >>


ECNextArriveGoRequest(f) ==
    /\ cabinTravelStatus # 0
    /\ goRequest[f] = 1
    /\ cabinLocation' = f
    /\ cabinTravelStatus' = 0
    /\ goRequest' = [goRequest EXCEPT ![f] = 0]
    /\ UNCHANGED << callRequest >>

ECNext ==
    \/ \E f \in Floors :
        \/ ECNextCall(f)
        \/ ECNextServiceCall(f)
        \/ ECNextArriveCall(f)
        \/ ECNextGoRequest(f)
        \/ ECNextServiceGoRequest(f)
        \/ ECNextArriveGoRequest(f)

vars == << cabinLocation, cabinTravelStatus, callRequest, goRequest >>

Spec == ECInit /\ [][ECNext]_vars    

(* Invariants
All of the things that should remain true in all states of our system.
*)
ECTypeOK ==
    /\ cabinLocation \in Floors
    /\ cabinTravelStatus \in {-1, 0, 1}
    /\ callRequest \in [Floors -> {0, 1}]
    /\ goRequest \in [Floors -> {0, 1}]

=============================================================================