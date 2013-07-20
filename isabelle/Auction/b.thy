theory b
imports Main Partitions 
begin

(*
(* Approach 1: Everything is a list *)
definition growpart 
::" 'a => 'a list list => 'a list => 'a list list"
where 
"growpart e X x = ( e # x ) # (removeAll x X)"

definition childrenofpartition (* given a partition p of X, obtain 
all the possible partitions of e#X being coarser than p*)
::" 'a => 'a list list => 'a list list list"
where 
"childrenofpartition e p =([e] # p ) # map (growpart e p) p"

definition partitionsconstructor 
::"'a => 'a list list list => 'a list list list "
where "partitionsconstructor e P = concat (map (childrenofpartition e) P)"

fun all_partitions ::" 'a list => 'a list list list"
where "all_partitions [] = [[]]"|
"all_partitions (e # X) = partitionsconstructor e (all_partitions X)"

definition all_partitions_set where (* Simplify all these [map, set] occurrences?*)
"all_partitions_set X = set (map set (map (map set) (all_partitions (sorted_list_of_set X))))"
*)

(* Approach 2: Everythin's a set, except the very initial input, which is a list (of elements)
because I don't know how to do recursive definitions on finite sets *)

(* CL@MC: please document the intuition behind this!  It would take me a lot of time to figure
   this out for myself by example. 
definition growpart
::"'a \<Rightarrow> ('a set \<times> ('a set set)) \<Rightarrow> 'a set set" 
where "growpart elem x=snd x - {fst x} \<union> {fst x \<union> {elem}}"

definition childrenofpartition 
::"'a => ('a set set) => ('a set set set)" 
where 
"childrenofpartition e p = insert (insert {e} p) ((growpart e) ` (p \<times> {p}))"
*)

end

