(*
$Id$

Auction Theory Toolbox

Authors:
* Marco B. Caminati <marco.caminati@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Preserving some stuff that we originally had in Partitions.thy,
  but which is no longer needed there, as List.thy does the same job well enough. *}

theory ListUtils
imports Main
begin

(* MC's old norepetitions is the same as List.distinct *)

lemma distinct_imp_card_eq_length: "distinct l \<longleftrightarrow> card (set l) = length l"
  by (metis card_distinct length_remdups_card_conv remdups_id_iff_distinct)

lemma "distinct l \<longleftrightarrow> (card (set l) \<ge> length l)" 
  using distinct_imp_card_eq_length by (metis card_length le_antisym)

(* MC's old noreptl existed in the library as List.distinct_tl *)

lemma finite_imp_length_sort_eq_card: fixes x assumes "finite x"
  shows "length (sorted_list_of_set x) = card x"
  using assms
  by (metis distinct_imp_card_eq_length sorted_list_of_set)

(* MC's old setlistid and norepset exist in the library as List.sorted_list_of_set *)

lemma remove_list_to_set: "set (x # removeAll y l) = insert x (set l - {y})" by simp

text {* mapping a function @{text f} over a distinct list @{text xs} yields a distinct list,
  if @{text f} returns unique results for each element of @{text xs}. *}
lemma distinct_map:
  shows "distinct xs \<Longrightarrow> \<forall> y \<in> set xs . f y \<notin> set (map f (remove1 y xs)) \<Longrightarrow> distinct (map f xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  note distinct = Cons.prems(1)
  note map_unique = Cons.prems(2)
  have prev_goal: "distinct (map f xs)"
    by (metis Cons.hyps distinct distinct.simps(2) in_set_member map.simps(2) map_unique member_rec(1) remove1.simps(2))
  have "remove1 x xs = xs"
    using distinct by (metis distinct.simps(2) remove1_idem)
  then have "f x \<notin> set (map f xs)"
    using map_unique by (metis not_Cons_self2 remove1.simps(2) remove1_idem)
  then have "distinct (f x # map f xs)" by (metis distinct.simps(2) prev_goal)
  then show ?case by simp
qed

end
