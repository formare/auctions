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

subsection {* Well-defined outcome *}

text {* well-definedness of an allocation, given the goods and participants: all goods are
  allocated within the set of participants; nothing is allocated twice. *}
(* TODO CL: allow for partial allocation: in this case, Domain x needs to be a 
   partition of a _subset_ of G *)
definition wd_allocation :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel \<Rightarrow> bool"
where "wd_allocation G N x \<longleftrightarrow> is_partition_of (Domain x) G \<and> Range x \<subseteq> N"

type_synonym outcome_well_definedness = "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation_rel \<Rightarrow> payments \<Rightarrow> bool"

definition wd_outcome :: "combinatorial_auction_rel \<Rightarrow> input_admissibility \<Rightarrow> outcome_well_definedness \<Rightarrow> bool"
where "wd_outcome A admissible wd_outcome_pred \<longleftrightarrow>
  (\<forall> ((G::goods, N::participant set, b::bids), (x::allocation_rel, p::payments)) \<in> A .
    admissible G N b \<longrightarrow> wd_outcome_pred G N b x p)"

text{* introduction rule for @{const wd_outcome}, to facilitate proofs of well-definedness of the outcome *}
lemma wd_outcomeI:
  assumes "\<And> G N b x p . ((G, N, b), (x, p)) \<in> A \<Longrightarrow> admissible G N b \<Longrightarrow> wd_outcome_pred G N b x p"
  shows "wd_outcome A admissible wd_outcome_pred"
(* CL: The following proof (tried before we added the "admissible" premise) takes 82 ms on my machine:
using assms unfolding wd_outcome_def by (smt prod_caseI2 prod_caseI2') *)
unfolding wd_outcome_def
proof
  fix T
  assume "T \<in> A"
  then obtain input out where T: "T = (input, out)" using PairE by blast
  from T obtain G N b where input: "input = (G, N, b)" using prod_cases3 by blast
  from T obtain x p where out: "out = (x, p)" using PairE by blast
  from input out T `T \<in> A` have "((G, N, b), (x, p)) \<in> A" by fastforce
  then have "admissible G N b \<longrightarrow> wd_outcome_pred G N b x p" using assms by fast
  with input out T
    show "case T of (input, out) \<Rightarrow> (\<lambda> (G, N, b) (x, p) . admissible G N b \<longrightarrow> wd_outcome_pred G N b x p) input out"
    using split_conv by force
qed

subsection {* Left-totality *}

text{* Left-totality of a combinatorial auction in relational form: for each admissible bid vector
  there exists some outcome (not necessarily unique nor well-defined). *}
definition left_total :: "combinatorial_auction_rel \<Rightarrow> input_admissibility \<Rightarrow> bool"
where "left_total A admissible \<longleftrightarrow> { (G, N, b) . admissible G N b } \<subseteq> Domain A"

text{* introduction rule for @{const left_total}, to facilitate left-totality proofs *}
lemma left_totalI:
  assumes "\<And> G N b . admissible G N b \<Longrightarrow> (\<exists> x p . ((G, N, b), (x, p)) \<in> A)"
  shows "left_total A admissible"
using assms unfolding left_total_def by fast

subsection {* Right-uniqueness *}

text{* Right-uniqueness of a combinatorial auction in relational form: for each admissible bid vector,
  if there is an outcome, it is unique.  This definition makes sense because we know @{thm runiq_restrict}. *}
definition right_unique :: "combinatorial_auction_rel \<Rightarrow> input_admissibility \<Rightarrow> bool"
where "right_unique A admissible \<longleftrightarrow> runiq (A || { (G, N, b) . admissible G N b })"

lemma right_uniqueI:
  assumes "\<And> G N b x x' p p' . admissible G N b
    \<Longrightarrow> ((G, N, b), (x, p)) \<in> A \<Longrightarrow> ((G, N, b), (x', p')) \<in> A
    \<Longrightarrow> x = x' \<and> p = p'"
  shows "right_unique A admissible"
proof -
  {
    fix input
    assume 1: "input \<in> {(G, N, b) . admissible G N b}"
    then obtain G N b where input: "input = (G, N, b)" by (auto simp add: prod_cases3)
    with 1 have adm: "admissible G N b" by fast
    fix out out'
    assume 2: "(input, out) \<in> A \<and> (input, out') \<in> A"
    then obtain x p x' p' where out: "out = (x, p)" and out': "out' = (x', p')" by fastforce
    from input 2 out have rel: "((G, N, b), (x, p)) \<in> A" by fast
    from input 2 out' have rel': "((G, N, b), (x', p')) \<in> A" by fast
    from adm rel rel' out out' have "out = out'" using assms by force
  }
  then have "\<forall> input \<in> {(G, N, b) . admissible G N b} . \<forall> out out' . (input, out) \<in> A \<and> (input, out') \<in> A \<longrightarrow> out = out'" by blast
  then show ?thesis unfolding right_unique_def using runiq_restrict by blast
qed

end

