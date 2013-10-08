(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Christoph Lange <math.semantic.web@gmail.com>

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

subsection {* Well-defined outcome *}

text {* No good is allocated to more than one bidder.  Given our formalisation of allocations 
  (relations between partitions of the set of goods and the set of bidders), this means that
  for each good the image of the equivalence class(es), in which the good occurs, under
  the allocation relation is @{const trivial}. *}
definition no_good_allocated_twice :: "goods \<Rightarrow> allocation_rel \<Rightarrow> bool"
where "no_good_allocated_twice G x \<longleftrightarrow> (\<forall> g \<in> G . trivial (x `` { P \<in> Domain x . g \<in> P }))"

text {* well-definedness of an allocation, given the goods and participants: all goods are
  allocated within the set of participants; nothing is allocated twice. *}
(* TODO CL: allow for partial allocation: in this case, Domain x needs to be a 
   partition of a _subset_ of G *)
(* CL: Here, we do not care whether every good actually gets allocated.  Our current implementation 
   does this, but I'm not sure this is a criterion against which the implementation should be verified. *)
definition wd_allocation :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel \<Rightarrow> bool"
where "wd_allocation G N x \<longleftrightarrow> 
  no_good_allocated_twice G x \<and>
  \<Union> Domain x \<subseteq> G (* only available goods are allocated *) \<and>
  Range x \<subseteq> N (* goods are only allocated among the bidders *)"

type_synonym outcome_well_definedness = "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation_rel \<Rightarrow> payments \<Rightarrow> bool"

definition wd_outcome :: "combinatorial_auction_rel \<Rightarrow> input_validity \<Rightarrow> outcome_well_definedness \<Rightarrow> bool"
where "wd_outcome A valid wd_outcome_pred \<longleftrightarrow>
  (\<forall> ((G::goods, N::participant set, b::bids), (x::allocation_rel, p::payments)) \<in> A .
    valid G N b \<longrightarrow> wd_outcome_pred G N b x p)"

text{* introduction rule for @{const wd_outcome}, to facilitate proofs of well-definedness of the outcome *}
lemma wd_outcomeI:
  assumes "\<And> G N b x p . ((G, N, b), (x, p)) \<in> A \<Longrightarrow> valid G N b \<Longrightarrow> wd_outcome_pred G N b x p"
  shows "wd_outcome A valid wd_outcome_pred"
(* CL: The following proof (tried before we added the "valid" premise) takes 82 ms on my machine:
using assms unfolding wd_outcome_def by (smt prod_caseI2 prod_caseI2') *)
unfolding wd_outcome_def
proof
  fix T
  assume "T \<in> A"
  then obtain input out where T: "T = (input, out)" using PairE by blast
  from T obtain G N b where input: "input = (G, N, b)" using prod_cases3 by blast
  from T obtain x p where out: "out = (x, p)" using PairE by blast
  from input out T `T \<in> A` have "((G, N, b), (x, p)) \<in> A" by fastforce
  then have "valid G N b \<longrightarrow> wd_outcome_pred G N b x p" using assms by fast
  with input out T
    show "case T of (input, out) \<Rightarrow> (\<lambda> (G, N, b) (x, p) . valid G N b \<longrightarrow> wd_outcome_pred G N b x p) input out"
    using split_conv by force
qed

subsection {* Left-totality *}

text{* Left-totality of a combinatorial auction in relational form: for each valid bid vector
  there exists some outcome (not necessarily unique nor well-defined). *}
definition left_total :: "combinatorial_auction_rel \<Rightarrow> input_validity \<Rightarrow> bool"
where "left_total A valid \<longleftrightarrow> { (G, N, b) . valid G N b } \<subseteq> Domain A"

text{* introduction rule for @{const left_total}, to facilitate left-totality proofs *}
lemma left_totalI:
  assumes "\<And> G N b . valid G N b \<Longrightarrow> (\<exists> x p . ((G, N, b), (x, p)) \<in> A)"
  shows "left_total A valid"
using assms unfolding left_total_def by fast

subsection {* Right-uniqueness *}

text{* Right-uniqueness of a combinatorial auction in relational form: for each valid bid vector,
  if there is an outcome, it is unique.  This definition makes sense because we know @{thm runiq_restrict}. *}
definition right_unique :: "combinatorial_auction_rel \<Rightarrow> input_validity \<Rightarrow> bool"
where "right_unique A valid \<longleftrightarrow> runiq (A || { (G, N, b) . valid G N b })"

lemma right_uniqueI:
  assumes "\<And> G N b x x' p p' . valid G N b
    \<Longrightarrow> ((G, N, b), (x, p)) \<in> A \<Longrightarrow> ((G, N, b), (x', p')) \<in> A
    \<Longrightarrow> x = x' \<and> p = p'"
  shows "right_unique A valid"
proof -
  {
    fix input
    assume 1: "input \<in> {(G, N, b) . valid G N b}"
    then obtain G N b where input: "input = (G, N, b)" by (auto simp: prod_cases3)
    with 1 have adm: "valid G N b" by fast
    fix out out'
    assume 2: "(input, out) \<in> A \<and> (input, out') \<in> A"
    then obtain x p x' p' where out: "out = (x, p)" and out': "out' = (x', p')" by fastforce
    from input 2 out have rel: "((G, N, b), (x, p)) \<in> A" by fast
    from input 2 out' have rel': "((G, N, b), (x', p')) \<in> A" by fast
    from adm rel rel' out out' have "out = out'" using assms by force
  }
  then have "\<forall> input \<in> {(G, N, b) . valid G N b} . \<forall> out out' . (input, out) \<in> A \<and> (input, out') \<in> A \<longrightarrow> out = out'" by blast
  then show ?thesis unfolding right_unique_def using runiq_restrict by blast
qed

subsection {* Overall soundness *}

text {* A combinatorial auction in relational form is sound if it is left-total, right-unique
  and yields a well-defined outcome. *}
definition sound :: "combinatorial_auction_rel \<Rightarrow> input_validity \<Rightarrow> outcome_well_definedness \<Rightarrow> bool"
where "sound A valid wd_outcome_pred \<longleftrightarrow>
  left_total A valid \<and>
  right_unique A valid \<and>
  wd_outcome A valid wd_outcome_pred"

end

