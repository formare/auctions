(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Makarius Wenzel <wenzel@lri.fr>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Fully specified single good auctions (with tie-breaking) *}

theory SingleGoodAuctionTieBreaker
(* TODO CL: consider renaming as per https://github.com/formare/auctions/issues/16 *)
imports Main
  "~~/src/HOL/Library/Order_Relation"
  SingleGoodAuction
begin

(*
CL: CR commented that a tie-breaker may even be employed on the highest level of ranking bids:
There's nothing, in principle, to prevent design of an auction in which the value of a bid is not the first element in the lexicographical order - or even, presumably - in which the scoring rule calculates a weighted average of a number of factors.
*)

text{* Helps to determine whether one participant should be preferred over another one in the case of a draw.
  t x y = True should result in x being (strictly) preferred. *}
type_synonym tie_breaker = "participant \<Rightarrow> participant \<Rightarrow> bool"

text{* Is a tie-breaker well-behaved on a given set of participants?  I.e. is it a strict
  linear order? *}
definition wb_tie_breaker_on :: "tie_breaker \<Rightarrow> participant set \<Rightarrow> bool"
  where "wb_tie_breaker_on t N \<longleftrightarrow>
    strict_linear_order_on N
      {(a::participant, b::participant) . {a, b} \<subseteq> N \<and> t a b}"
(* old version for tie_breaker = "participant \<Rightarrow> real", to be used with <
   "card (tie_breaker ` N) = card N" *)

(* CL: code provided by Le_J (http://stackoverflow.com/a/16690357/2397768) –
   how to prove strict linear order in a concrete case: *)
(*
lemma "strict_linear_order_on {1::nat, 2} {(a::nat, b) . {a, b} \<subseteq> {1::nat, 2} \<and> a < b}"
  unfolding strict_linear_order_on_def partial_order_on_def preorder_on_def
    irrefl_def total_on_def trans_def antisym_def
  by auto
*)

end
