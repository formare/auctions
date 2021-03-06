(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Christoph Lange <math.semantic.web@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Additional material that we would have expected in Finite_Set.thy *}

theory Finite_SetUtils
imports
  Main

begin

section {* cardinality *}

(*
text {* A set of non-zero cardinality is not empty *}
lemma card_gt_0_imp_non_empty:
  fixes A::"'a set"
  assumes "card A > 0"
  shows "A \<noteq> {}"
using assms by fastforce

text {* A finite, non-empty set (i.e.\ having a non-zero cardinality) has a member. *}
lemma card_gt_0_imp_member:
  fixes A::"'a set"
  assumes "card A > 0"
  obtains y where "y \<in> A"
using assms by fastforce
*)
end
