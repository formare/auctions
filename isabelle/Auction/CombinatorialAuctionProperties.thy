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

header {* Some properties that combinatorial auctions can have *}

theory CombinatorialAuctionProperties
imports CombinatorialAuction

begin

(* TODO CL: revise the following as per https://github.com/formare/auctions/issues/19 *)

section {* Soundness *}

section {* Admissible input *}

type_synonym input_admissibility = "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> bool"

text {* Admissible input (i.e.\ admissible bids, given the goods and participants).  As we represent
  @{typ bids} as functions, which are always total in Isabelle/HOL, we can't test, e.g., whether
  their domain is @{term "G \<times> N"} for the given goods @{term G} and participants @{term N}. *}
(* CL: This definition is not currently useful, but once we realise general/special auctions using
   locales, we need an admissible_input axiom. *)
definition admissible_input :: "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> bool"
where "admissible_input G N b = True"

subsection {* Well-defined outcome *}

text {* well-definedness of an allocation, given the goods and participants: all goods are
  allocated within the set of participants *}
definition wd_allocation :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel \<Rightarrow> bool"
where "wd_allocation G N x \<longleftrightarrow> is_partition_of (Domain x) G \<and> Range x \<subseteq> N"

type_synonym outcome_well_definedness = "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation_rel \<Rightarrow> payments \<Rightarrow> bool"

definition wd_outcome :: "combinatorial_auction \<Rightarrow> outcome_well_definedness \<Rightarrow> bool"
where "wd_outcome A wd_outcome_pred \<longleftrightarrow>
  (\<forall> ((G::goods, N::participant set, b::bids), (x::allocation_rel, p::payments)) \<in> A .
    wd_outcome_pred G N b x p)"

subsection {* Left-totality *}

text{* Left-totality of a combinatorial auction in relational form: for each admissible bid vector
  there exists some outcome (not necessarily unique nor well-defined). *}
definition left_total :: "combinatorial_auction \<Rightarrow> input_admissibility \<Rightarrow> bool"
where "left_total A admissible \<longleftrightarrow> { (G, N, b) . admissible G N b } \<subseteq> Domain A"

(* TODO CL: maybe we need a counterpart to SingleGoodAuctionProperties.sga_left_totalI here as well *)

subsection {* Right-uniqueness *}

text{* Right-uniqueness of a combinatorial auction in relational form: for each admissible bid vector,
  if there is an outcome, it is unique.  This definition makes sense because we know @{thm runiq_restrict}. *}
definition right_unique :: "combinatorial_auction \<Rightarrow> input_admissibility \<Rightarrow> bool"
where "right_unique A admissible \<longleftrightarrow> runiq (A || { (G, N, b) . admissible G N b })"

end

