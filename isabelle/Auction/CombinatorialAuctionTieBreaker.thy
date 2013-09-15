(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Tie-breakers in Combinatorial Auctions *}

theory CombinatorialAuctionTieBreaker
imports
  CombinatorialAuction

begin

text {* This formalisation includes suggestions from two participants in a 
  \href{http://stackoverflow.com/questions/18806628/why-is-my-definition-of-a-function-that-chooses-an-element-from-a-finite-set-inc}{discussion at StackOverflow}. *}

section {* Types *}

type_synonym tie_breaker_rel = "allocation_rel set \<Rightarrow> allocation_rel"
type_synonym tie_breaker_alg = "allocation_rel list \<Rightarrow> allocation_rel"
(* CL: probably not needed, neither for close-to-paper nor for computable version
type_synonym tie_breaker_fun = "allocation_fun set \<Rightarrow> allocation_fun"
*)

text {* A well-defined tie-breaker is a \href{http://en.wikipedia.org/wiki/Choice_function}{choice function}
  that selects one element out of a set of allocations. *}
definition tie_breaker :: "tie_breaker_rel \<Rightarrow> bool"
where "tie_breaker t \<longleftrightarrow> (\<forall> X . X \<noteq> {} \<longrightarrow> t X \<in> X)"

text {* break ties by preferring an arbitrary existing allocation using the choice operator *}
definition tie_breaker_choice :: "tie_breaker_rel" where "tie_breaker_choice x = (SOME y . y \<in> x)"

text {* @{const tie_breaker_choice} is a valid tie-breaker. *}
lemma "tie_breaker tie_breaker_choice"
unfolding tie_breaker_def tie_breaker_choice_def
by (metis (lifting) all_not_in_conv some_eq_ex)

(* TODO CL: when proving paper\<longleftrightarrow>algorithm equivalence w.r.t. tie-breakers, we need to make the
   assumption, that the "set" tie-breaker and the "list" tie-breaker select the same allocation. *)
text {* trivial algorithmic tie breaker: take the first element of a list *}
definition tie_breaker_example_alg :: tie_breaker_alg where "tie_breaker_example_alg = hd"

end

