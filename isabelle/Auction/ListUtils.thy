(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

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

lemma set_concat: "set (concat xss) = \<Union> {set xs | xs . xs \<in> set xss}" (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS" by auto
next
  show "?RHS \<subseteq> ?LHS" by auto
qed

end
