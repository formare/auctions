theory ListUtils

imports Main 
"~~/src/HOL/Library/Code_Target_Nat" 

begin
(* Takes a list and breaks it into contiguous sublists at the points specified by indexList.
This gives a specific partition of the original list.
It is responsibility of the user to make sure that indexList is a sorted and remdupsed natlist,
having entries lying in the appropriate range.*)
abbreviation "breakList' indexList list == 
(% il l. let IL=(0#il@[size l]) in [sublist l {IL!(n-1)..<IL!n}. n<-[1..<size IL]]) indexList list"
value "breakList' [3,6,9] [1..<11::nat]"

abbreviation "breakListEvenly' period list == 
breakList' (map (op * period) [1 ..< 1+((size list - 1) div period)]) list"
value "((breakListEvenly' 3 [0..<11]), transpose (breakListEvenly' 3 [0..<11]))"
abbreviation "pairWise Op l m == [Op (l!i) (m!i). i <- [0..<min (size l) (size m)]]"
lemma lm01: assumes "n\<in>{0..<min (size l) (size m)}" shows "(pairWise Op l m)!n = Op (l!n) (m!n)"
using assms by auto
definition "droplast list = take (size list - 1) list"
abbreviation "lastElem list == list!(size list - 1)"
end
