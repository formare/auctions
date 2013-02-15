(*
$Id$

Auction Theory Toolbox

Authors:
* Manfred Kerber <m.kerber@cs.bham.ac.uk>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Makarius Wenzel <wenzel@lri.fr>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)


header {* Some examples for testing SingleGoodAuction *}

theory SingleGoodAuctionTest
imports SingleGoodAuction
begin

subsection {* Allocation *}

subsubsection {* Sample lemma: The allocation, in which the first participant wins (whatever the bids) is an allocation. *}

definition all_bid_1 :: "real_vector" where
   "all_bid_1 = (\<lambda>x. 1)"

(* TODO CL: document that, in contrast to Theorema, Isabelle can't _compute_ universal quantification in the finite case.
value "bids 1 all_bid_1"
*)

lemma bid_all_bid_1:
  shows "bids 1 all_bid_1"
  apply(unfold bids_def all_bid_1_def)
  apply(unfold non_negative_real_vector_def)
  apply(auto)
done

definition first_wins :: "allocation"
where
  "first_wins _ i \<longleftrightarrow> i = 1" (* whatever the bids, the first participant wins *)

(* for testing
lemma only_wins_is_allocation:
  shows "allocation 1 all_bid_1 first_wins"
apply(unfold allocation_def)
apply(unfold true_for_exactly_one_member_def)
apply(unfold first_wins_def)
apply(auto)
apply(rule bid_all_bid_1)
apply(blast)
done
*)

(* TODO CL: note that this is a more tactic-free syntax; I think here it doesn't really make sense to write down explicit proof steps.
lemma only_wins_is_allocation_declarative:
  shows "allocation 1 all_bid_1 first_wins"
  unfolding allocation_def true_for_exactly_one_member_def first_wins_def using bid_all_bid_1
  by auto *)


subsection {* Payoff *}

(* for testing *)
value "payoff 5 True 2" (* I ascribed the value 5 to the good, won the auction, and had to pay 2. *)

end
