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
  shows "left_total (nVCG_auctions t) valid_input"
proof (rule left_totalI)
  fix G::goods and N::"participant set" and b::bids
  assume assm: "valid_input G N b"
  def x \<equiv> "winning_allocation_rel G N t b" (* these are function values and therefore guaranteed to exist *)
  def p \<equiv> "payments_rel G N t b"
  from assm x_def p_def have "nVCG_pred t G N b x p" unfolding nVCG_pred_def by blast
  then show "\<exists> x p . ((G, N, b), (x, p)) \<in> nVCG_auctions t"
    unfolding nVCG_auctions_def using pred_imp_rel_all by metis
qed

section {* right-unique *}

text {* splits the outcome of a combinatorial Vickrey auction in relational form into 
  allocation and payment *}
lemma split_outcome:
  assumes "((G, N, b), (x, p)) \<in> nVCG_auctions t"
  shows "x = winning_allocation_rel G N t b \<and> p = payments_rel G N t b"
proof -
  from assms have "pred_tup (nVCG_pred t) ((G, N, b), (x, p))"
    unfolding nVCG_auctions_def rel_all_def by fast
  then show "x = winning_allocation_rel G N t b \<and> p = payments_rel G N t b"
    unfolding pred_tup_def nVCG_pred_def by blast
qed

text {* The combinatorial Vickrey auction in relational form is right-unique.  This is easy to 
  show because its outcome is defined by two functions, which are right-unique by construction. *}
lemma right_unique:
  fixes t::tie_breaker_rel (* no need to assume anything about t *)
  shows "right_unique (nVCG_auctions t) valid_input"
proof (rule right_uniqueI)
  fix G::goods and N::"participant set" and b::bids
  (* As right-uniqueness is so easy to prove in this case, 
     it turns out that we don't need the additional assumption "valid_input G N b". *)
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
  shows "wd_outcome (nVCG_auctions t) valid_input wd_alloc_pay"
proof (rule wd_outcomeI)
  fix G N b x p
  assume "((G, N, b), (x, p)) \<in> nVCG_auctions t"
  then have xp: "x = winning_allocation_rel G N t b \<and> p = payments_rel G N t b" by (rule split_outcome)

  assume valid: "valid_input G N b"
  from xp have x_unfolded: "x = t (arg_max' (value_rel b) (possible_allocations_rel G N))"
    unfolding winning_allocation_rel.simps winning_allocations_rel_def
    by simp

  have alloc_non_empty: "arg_max' (value_rel b) (possible_allocations_rel G N) \<noteq> {}"
  proof -
    from valid have "card G > 0" and "card N > 0" unfolding valid_input_def by simp_all

    from `card G > 0` have "finite G" by (rule card_ge_0_finite)
    from `card N > 0` have "finite N" by (rule card_ge_0_finite)

    from `card G > 0` have "G \<noteq> {}" by force
    then have "is_partition_of {G} G" by (rule set_partitions_itself)
    then have *: "{G} \<in> all_partitions G" unfolding all_partitions_def by (rule CollectI)
    moreover have "injections {G} N \<noteq> {}"
    proof -
      have "finite {G}" by simp
      moreover note `finite N`
      moreover have "card {G} \<le> card N" using `card N > 0` by auto
      ultimately show ?thesis by (rule injections_exist)
    qed
    ultimately have "(* \<Union> { injections Y N | Y . Y \<in> all_partitions G } = *)
      possible_allocations_rel G N \<noteq> {}"
      by (auto simp add: Union_map_non_empty)
    moreover have "finite (possible_allocations_rel G N)"
    proof -
      from `finite G` have "finite (all_partitions G)" by (rule finite_all_partitions)
      moreover {
        fix Y
        assume "Y \<in> all_partitions G"
        then have "\<Union> Y = G" unfolding all_partitions_def is_partition_of_def
          by (metis (lifting, full_types) mem_Collect_eq)
        with `finite G` have "finite Y" by (metis finite_UnionD)
        then have "finite (injections Y N)" using `finite N` by (rule finite_injections)
      }
      ultimately have "finite (\<Union> Y \<in> all_partitions G . injections Y N)" by (rule finite_UN_I)
      then show ?thesis by (simp add: Union_set_compr_eq)
    qed
    ultimately have "arg_max' (value_rel b) (possible_allocations_rel G N) \<noteq> {}"
      by (rule arg_max'_non_empty_iff)
    then show ?thesis by fast
  qed
  with assms x_unfolded have "x \<in> arg_max' (value_rel b) (possible_allocations_rel G N)"
    using tie_breaker_def by smt
  then have "x \<in> { x \<in> \<Union> { injections Y N | Y . Y \<in> all_partitions G } .
    value_rel b x = Max ((value_rel b) ` \<Union> { injections Y N | Y . Y \<in> all_partitions G }) }" by simp
  then have "x \<in> \<Union> { injections Y N | Y . Y \<in> all_partitions G }
    \<and> value_rel b x = Max ((value_rel b) ` \<Union> { injections Y N | Y . Y \<in> all_partitions G })"
    by (rule CollectD)
  then have x_alloc: "x \<in> \<Union> { injections Y N | Y . Y \<in> all_partitions G }" ..
  then have "\<exists> Y \<in> all_partitions G . x \<in> injections Y N" by (rule Union_map_member)
  then obtain Y where part: "Y \<in> all_partitions G" and inj: "x \<in> injections Y N" by fast

  from part have "is_partition_of Y G" unfolding all_partitions_def by (rule CollectD)
  moreover have "Domain x = Y" using inj unfolding injections_def by simp
  ultimately have "is_partition_of (Domain x) G" by blast

  from xp (* to use Max_in, we need additional assumptions about N and G, so that \<Union> is non-empty *)
    have p_unfolded: "p = (\<lambda>n . (Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))))
      - (\<Sum> m \<in> N - {n} . b m (eval_rel_or (x\<inverse>) m {})))" by fastforce

  have "wd_allocation G N x"
  proof -
    have "no_good_allocated_twice G x" unfolding no_good_allocated_twice_def
    proof
      fix g assume "g \<in> G"
      from inj have "runiq x" unfolding injections_def by simp
      moreover have "trivial { P \<in> Domain x . g \<in> P }"
      proof -
        {
          fix a b assume a: "a \<in> { P \<in> Domain x . g \<in> P }" and b: "b \<in> { P \<in> Domain x . g \<in> P }"
          have a': "a \<in> Domain x" and "g \<in> a" using a by simp_all
          have b': "b \<in> Domain x" and "g \<in> b" using b by simp_all
          from `g \<in> a` `g \<in> b` have "a \<inter> b \<noteq> {}" by blast
          with `is_partition_of (Domain x) G`
            have "a = b"
            unfolding is_partition_of_def is_partition_def
            using a' b' by simp
        }
        then show ?thesis by (simp add: no_distinct_imp_trivial)
      qed
      ultimately show "trivial (x `` { P \<in> Domain x . g \<in> P })" by (auto simp only: runiq_def)
    qed
    moreover have "\<Union> Domain x \<subseteq> G" using `is_partition_of (Domain x) G` unfolding is_partition_of_def by blast
    moreover have "Range x \<subseteq> N" using inj unfolding injections_def by simp
    ultimately show ?thesis unfolding wd_allocation_def by blast
  qed
  moreover have "wd_payments N p" unfolding wd_payments_def
  proof
    fix n assume "n \<in> N"
    from p_unfolded have "p n = (Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))))
      - (\<Sum> m \<in> N - {n} . b m (eval_rel_or (x\<inverse>) m {}))" by fast
    moreover have "Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))) \<ge> (\<Sum> m \<in> N - {n} . b m (eval_rel_or (x\<inverse>) m {}))" sorry
    ultimately show "p n \<ge> 0" by fastforce
  qed
  ultimately show "wd_alloc_pay G N b x p" unfolding wd_alloc_pay_def ..
qed

section {* Overall soundness *}

text {* The combinatorial Vickrey auction is sound. *}
theorem sound:
  fixes t::tie_breaker_rel (* no need to assume anything about t *)
  assumes "tie_breaker t"
  shows "sound (nVCG_auctions t) valid_input wd_alloc_pay"
proof -
  note left_total
  moreover note right_unique
  moreover have "wd_outcome (nVCG_auctions t) valid_input wd_alloc_pay"
    using assms by (rule wd_outcome)
  ultimately show ?thesis unfolding sound_def by blast
qed

end

