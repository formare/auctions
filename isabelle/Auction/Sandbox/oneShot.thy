theory oneShot

imports
  Rat
  Main
  "~~/src/HOL/Library/Code_Target_Nat"
  "../Vcg/Argmax"
  "../Vcg/Universes"  

begin 

(*
We start from the following data:

- a list of tasks
- for each participant, two lists of tasks: the ones he likes, in order of preference, 
  and the ones he doesn't, in decreasing preference: [best, second best, ...], [worst, second worst, ...]

We want to assign the tasks under the following criteria :

- No one has to have more than maxTasks assigned, at the end (this is yet to be implemented)
- The total happiness must be maximal: the happiness for one participant is calculated by 
adding 1/n for the nth favorite task, if assigned to him, and by subtracting 1/m for the mth 
most displeased task, if assigned to him.
*)

abbreviation "maxTasks == 3"

abbreviation "happiness1p favourites1p unfavourites1p assignment == 
              listsum [ let j=rat_of_nat (i+1) in 1/j. 
                        i<-[0..<size favourites1p], favourites1p!i \<in> assignment ]-
              listsum [ let j=rat_of_nat (i+1) in 1/j. i<-[0..<size unfavourites1p], unfavourites1p!i \<in> assignment ]"
              
abbreviation "extractParticipant p l == l ! (hd (filterpositions2 (% x. fst x=p) l))"

(* An allocation has the form {(participant, {task1, task2}), ...} *)
abbreviation "happiness favourites unfavourites allocation == 
              setsum (% participant. happiness1p (favourites,,participant) (unfavourites,,participant) (allocation,,participant))
              (Domain allocation)"

(* This returns the allocations maximizing happiness, in the form of a set of allocations. *)              
abbreviation "optimalAllocations taskList favourites unfavourites == 
              argmax (happiness favourites unfavourites)
                      (set (possibleAllocationsAlg (Domain favourites) taskList))"

value "optimalAllocations [10::nat, 11] {(1::nat, [13])} {(1::nat, [13])}"

(* Possible ideas to be further implemented: 
- In a preliminary step, we remove the tasks falling under exactly one favourite list
- The maxTasks could be used to limit the computational effort when calculating the possible partitions
- Use lists instead of sets as much as possible
- Try to find in Java a way of computing allocations: it seems difficult to give up the concept of allocation,
since the global happiness depends on the set of all participants.
*)

end

