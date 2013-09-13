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

header {* Soundness verification of the combinatorial Vickrey auction *}

theory CombinatorialVickreyAuctionSoundness
imports
  CombinatorialVickreyAuction
  CombinatorialAuctionProperties
  
begin

section {* left-total *}

text {* The combinatorial Vickrey auction in relational form is left-total.
  Note that in Isabelle/HOL's logic of total functions, an outcome (allocation @{term x} and
  @{term p}) will always trivially exist, as they are return values of functions.  It is more
  interesting to prove that the outcome of our auction is \emph{well-defined}. *}
lemma left_total:
  fixes t::tie_breaker_rel (* no need to assume anything about t *)
  shows "left_total (nVCG_auctions t) admissible_input"
proof (rule left_totalI)
  fix G::goods and N::"participant set" and b::bids
  assume assm: "admissible_input G N b"
  def x \<equiv> "winning_allocation_rel G N t b"
  def p \<equiv> "payments_rel G N t b"
  from assm x_def p_def have "nVCG_pred t G N b x p" unfolding nVCG_pred_def by blast
  then show "\<exists> x p . ((G, N, b), (x, p)) \<in> nVCG_auctions t"
    unfolding nVCG_auctions_def using pred_imp_rel_all by metis
qed

section {* right-unique *}

text {* splits the outcome of a combinatorial Vickrey auction in relational form into 
  allocation and payment *}
lemma split_outcome:
  assumes "((G', N', b'), (x'', p'')) \<in> nVCG_auctions t"
  shows "x'' = winning_allocation_rel G' N' t b' \<and> p'' = payments_rel G' N' t b'"
proof -
  from assms have "pred_tup (nVCG_pred t) ((G', N', b'), (x'', p''))"
    unfolding nVCG_auctions_def rel_all_def by fast
  then show "x'' = winning_allocation_rel G' N' t b' \<and> p'' = payments_rel G' N' t b'"
    unfolding pred_tup_def nVCG_pred_def by blast
qed

text {* The combinatorial Vickrey auction in relational form is right-unique.  This is easy to 
  show because its outcome is defined by two functions, which are right-unique by construction. *}
lemma right_unique:
  fixes t::tie_breaker_rel (* no need to assume anything about t *)
  shows "right_unique (nVCG_auctions t) admissible_input"
proof (rule right_uniqueI)
  fix G::goods and N::"participant set" and b::bids
  (* As right-uniqueness is so easy to prove in this case, 
     it turns out that we don't need the additional assumption "admissible_input G N b". *)
  fix x::allocation_rel and x'::allocation_rel and p::payments and p'::payments

  assume "((G, N, b), (x, p)) \<in> nVCG_auctions t"
  then have xp: "x = winning_allocation_rel G N t b \<and> p = payments_rel G N t b" by (rule split_outcome)
  assume "((G, N, b), (x', p')) \<in> nVCG_auctions t"
  then have xp': "x' = winning_allocation_rel G N t b \<and> p' = payments_rel G N t b" by (rule split_outcome)

  from xp xp' show "x = x' \<and> p = p'" by fast
qed

section {* well-defined outcome *}

text {* Payments are well-defined if every bidder has to pay a non-negative amount. *}
(* CL: not sure whether we should define this here, or in CombinatorialAuction.  Maybe it is useful 
   for other combinatorial auctions too. *)
definition wd_payments :: "participant set \<Rightarrow> payments \<Rightarrow> bool"
where "wd_payments N p \<longleftrightarrow> (\<forall> n \<in> N . p n \<ge> 0)"

text {* The outcome of the combinatorial Vickrey auction is well-defined, if the allocation 
  is well-defined and the payments are non-negative. *}
definition wd_alloc_pay :: "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation_rel \<Rightarrow> payments \<Rightarrow> bool"
where "wd_alloc_pay G N b x p \<longleftrightarrow> wd_allocation G N x \<and> wd_payments N p"

text {* The combinatorial Vickrey auction is well-defined. *}
lemma wd_outcome:
  fixes t::tie_breaker_rel
  assumes "tie_breaker t"
  shows "wd_outcome (nVCG_auctions t) admissible_input wd_alloc_pay"
proof (rule wd_outcomeI)
  fix G N b x p
  assume "((G, N, b), (x, p)) \<in> nVCG_auctions t"
  then have xp: "x = winning_allocation_rel G N t b \<and> p = payments_rel G N t b" by (rule split_outcome)

  from xp have "x = t { potential_buyer . value_rel b potential_buyer
     = Max ((value_rel b) ` \<Union> { injections Y N | Y . Y \<in> all_partitions G }) }"
    unfolding winning_allocation_rel.simps winning_allocations_rel_def
    by simp
  with assms have x_unfolded': "value_rel b x
     = Max ((value_rel b) ` \<Union> { injections Y N | Y . Y \<in> all_partitions G })"
     using tie_breaker_def by blast
  from xp (* to use Max_in, we need additional assumptions about N and G, so that \<Union> is non-empty *)
    have p_unfolded: "p = (\<lambda>n . (Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))))
      - (\<Sum> m \<in> N - {n} . b m (eval_rel_or (x\<inverse>) m {})))" by fastforce
  
  have "wd_allocation G N x" unfolding wd_allocation_def
  proof
    show "is_partition_of (Domain x) G" sorry
    show "Range x \<subseteq> N" sorry
  qed
  moreover have "wd_payments N p" unfolding wd_payments_def
  proof
    fix n assume "n \<in> N"
    then show "p n \<ge> 0" sorry
  qed
  ultimately show "wd_alloc_pay G N b x p" unfolding wd_alloc_pay_def ..
qed

end

