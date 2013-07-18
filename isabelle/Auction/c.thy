theory c

imports Main
(* "~~/src/HOL/Imperative_HOL/ex/Sublist" *)

begin
(*
lemma 1: shows "(sublist [] {0..<1})@(sublist [] {1..< (length [])}) = 
(sublist [] {0..< (length l)})" by auto

lemma 2: fixes l assumes "length l > 0" shows "(sublist l {0..<1})@(sublist l {1..<(length l)})=
sublist l {0..<length l}" using sublist_split by (smt assms)

lemma listsplit: fixes l shows "(sublist l {0..<1})@(sublist l {1..<(length l)})=
l" using 1 2 by (metis length_greater_0_conv sublist_all')

lemma fixes l shows "l = sublist l {0..<(length l)}" by force

lemma hdsub: assumes "l \<noteq> []" shows "sublist l {0} = [hd l]" 
by (metis assms hd_conv_nth length_greater_0_conv sublist_single)

lemma fixes l shows "(hd l)#(map (nth l) (upt 1 (size l)))=l" 

*)

definition norepetitions 
::"'a list => bool"
where "norepetitions l \<longleftrightarrow> card (set l) = length l"

lemma fixes l shows "norepetitions l \<longleftrightarrow> (card (set l) \<ge> length l)" 
using norepetitions_def by (metis card_length le_antisym)

lemma noreptl: fixes l assumes "norepetitions l" shows "norepetitions (tl l)" 
using assms norepetitions_def by (metis card_distinct distinct_card distinct_tl) 

lemma norepdrop: fixes l n assumes "norepetitions l" shows "norepetitions (drop n l)" 
using assms norepetitions_def by (metis card_distinct distinct_card distinct_drop)

lemma fixes l assumes "l \<noteq> []" shows "l!0=hd l" using assms by (metis hd_conv_nth)

lemma fixes x assumes "finite x"
shows "length (sorted_list_of_set x) = card x" 
using assms by 
(metis finite_list length_remdups_card_conv length_sort sorted_list_of_set_sort_remdups)

end

