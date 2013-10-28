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
  Big_OperatorsUtils
  
begin

section {* left-total *}

text {* The combinatorial Vickrey auction in relational form is left-total.
  Note that in Isabelle/HOL's logic of total functions, an outcome (allocation @{term x} and
  @{term p}) will always trivially exist, as they are return values of functions.  It is more
  interesting to prove that the outcome of our auction is \emph{well-defined}. *}
lemma left_total:
  fixes t::tie_breaker_rel (* no need to assume anything about t *)
  shows "left_total (nVCG_auctions t) valid_input"
(* CL: In Isabelle2013-1-RC2 the following takes 239 ms: 
   by (metis CombinatorialAuctionProperties.left_totalI nVCG_auctions_def nVCG_pred_def pred_imp_rel_all) *)
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

text {* In a valid input to a combinatorial Vickrey auction, the set of goods in particular
  has a non-zero cardinality. *}
lemma card_goods_gt_0:
  assumes "valid_input G N b"
  shows "card G > 0"
using assms
unfolding valid_input_def CombinatorialAuction.valid_input_def
by simp

text {* In a valid input to a combinatorial Vickrey auction, the set of goods in particular
  is finite. *}
lemma finite_goods:
  assumes "valid_input G N b"
  shows "finite G"
proof -
  from assms have "card G > 0" by (rule card_goods_gt_0)
  then show ?thesis by (rule card_ge_0_finite)
qed

text {* In a valid input to a combinatorial Vickrey auction, the set of participants in particular
  has a non-zero cardinality. *}
lemma card_participants_gt_0:
  assumes "valid_input G N b"
  shows "card N > 0"
using assms
unfolding valid_input_def CombinatorialAuction.valid_input_def
by simp

text {* In a valid input to a combinatorial Vickrey auction, the set of participants in particular
  is finite. *}
lemma finite_participants:
  assumes "valid_input G N b"
  shows "finite N"
proof -
  from assms have "card N > 0" by (rule card_participants_gt_0)
  then show "finite N" by (rule card_ge_0_finite)
qed

text {* In a valid input to a combinatorial Vickrey auction, the set of participants in particular
  is finite, and (of course) this also holds after removing one participant from it. *}
lemma finite_participants_except:
  assumes "valid_input G N b"
  shows "finite (N - {n})"
proof -
  from assms have "finite N" by (rule finite_participants)
  then show ?thesis by force
qed

text {* The outcome of the combinatorial Vickrey auction is well-defined, if the allocation 
  is well-defined and the payments are non-negative. *}
definition wd_alloc_pay :: "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation_rel \<Rightarrow> payments \<Rightarrow> bool"
where "wd_alloc_pay G N b x p \<longleftrightarrow> wd_allocation G N x \<and> wd_payments N p"

text {* Given valid input, the winning allocation of a combinatorial Vickrey auction 
  is an injective relation. *}
lemma winning_allocation_injective:
  fixes G::goods
    and N::"participant set"
    and t::tie_breaker_rel
    and b::bids
  assumes valid_input: "valid_input G N b"
      and tie_breaker: "tie_breaker t"
  obtains Y
    where "Y \<in> all_partitions G"
      and "winning_allocation_rel G N t b \<in> injections Y N"
proof -
  have alloc_unfolded: "winning_allocation_rel G N t b = t (arg_max' (value_rel b) (possible_allocations_rel G N))"
    unfolding winning_allocation_rel.simps winning_allocations_rel_def
    by simp
  have alloc_non_empty: "arg_max' (value_rel b) (possible_allocations_rel G N) \<noteq> {}"
  proof -
    from valid_input have "card G > 0" by (rule card_goods_gt_0)
    then have "finite G" by (rule card_ge_0_finite)
    from valid_input have "card N > 0" by (rule card_participants_gt_0)
    then have "finite N" by (rule card_ge_0_finite)

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
      using `finite G` `finite N` by (rule allocs_finite)
    ultimately have "arg_max' (value_rel b) (possible_allocations_rel G N) \<noteq> {}"
      by (rule arg_max'_non_empty_iff)
    then show ?thesis by fast
  qed
  with tie_breaker alloc_unfolded
    have "winning_allocation_rel G N t b \<in> arg_max' (value_rel b) (possible_allocations_rel G N)"
    using tie_breaker_def by smt
  then have "winning_allocation_rel G N t b \<in> { x \<in> \<Union> { injections Y N | Y . Y \<in> all_partitions G } .
    value_rel b x = Max ((value_rel b) ` \<Union> { injections Y N | Y . Y \<in> all_partitions G }) }" by simp
  then have "winning_allocation_rel G N t b \<in> \<Union> { injections Y N | Y . Y \<in> all_partitions G }
    \<and> value_rel b (winning_allocation_rel G N t b) = Max ((value_rel b) ` \<Union> { injections Y N | Y . Y \<in> all_partitions G })"
    by (rule CollectD)
  then have x_alloc: "winning_allocation_rel G N t b \<in> \<Union> { injections Y N | Y . Y \<in> all_partitions G }" ..
  then have "\<exists> Y \<in> all_partitions G . winning_allocation_rel G N t b \<in> injections Y N" by (rule Union_map_member)
  then obtain Y where "Y \<in> all_partitions G" and "winning_allocation_rel G N t b \<in> injections Y N" by fast
  then show ?thesis ..
qed

text {* determine the winning allocation, but take out the tuple of participant @{term n} *}
fun winning_allocation_except
where "winning_allocation_except G N t b n = { (y::goods, m::participant) .
  (y::goods, m::participant) \<in> winning_allocation_rel G N t b \<and> m \<noteq> n }"

lemma winning_allocation_except_subrel:
  "winning_allocation_except G N t b n \<subseteq> winning_allocation_rel G N t b"
by fastforce

text {* an alternative way of expressing @{term remaining_value_rel}, by summing over equivalence
  classes in an allocation rather than over bidders *}
lemma remaining_value_alt:
  assumes valid_input: "valid_input G N b"
      and tie_breaker: "tie_breaker t"
  shows "remaining_value_rel G N t b n = value_rel b (winning_allocation_except G N t b n)"
proof -
  from assms obtain Y where "Y \<in> all_partitions G" and inj: "winning_allocation_rel G N t b \<in> injections Y N"
    by (rule winning_allocation_injective)
  from inj have runiq_alloc: "runiq (winning_allocation_rel G N t b)" unfolding injections_def by simp
  from inj have runiq_alloc_conv: "runiq ((winning_allocation_rel G N t b)\<inverse>)" unfolding injections_def by simp
  from inj have alloc_Range: "Range (winning_allocation_rel G N t b) \<subseteq> N" unfolding injections_def by simp

  from runiq_alloc winning_allocation_except_subrel have alloc_except_runiq: "runiq (winning_allocation_except G N t b n)" by (rule subrel_runiq)
  from winning_allocation_except_subrel have "(winning_allocation_except G N t b n)\<inverse> \<subseteq> (winning_allocation_rel G N t b)\<inverse>" by fastforce
  with runiq_alloc_conv have alloc_except_conv_runiq: "runiq ((winning_allocation_except G N t b n)\<inverse>)" by (rule subrel_runiq)
  from alloc_Range have alloc_except_Range: "Range (winning_allocation_except G N t b n)
    = (N - {n}) \<inter> Range (winning_allocation_rel G N t b)"
    unfolding winning_allocation_except.simps by (rule Range_except)

  have "remaining_value_rel G N t b n = (\<Sum> m \<in> N - {n} . b m (eval_rel_or ((winning_allocation_rel G N t b)\<inverse>) m {}))" by simp
  also have "\<dots> = (\<Sum> m \<in> N - {n} . b m (if m \<in> Domain ((winning_allocation_rel G N t b)\<inverse>) then the_elem (((winning_allocation_rel G N t b)\<inverse>) `` {m}) else {}))"
  proof -
    {
      fix m
      from runiq_alloc_conv have "eval_rel_or ((winning_allocation_rel G N t b)\<inverse>) m {}
        = (if m \<in> Domain ((winning_allocation_rel G N t b)\<inverse>) then the_elem (((winning_allocation_rel G N t b)\<inverse>) `` {m}) else {})"
        by (rule eval_runiq_rel_or)
    }
    then show ?thesis by presburger (* TODO CL: ask why "try" finds sledgehammer proofs > 3s in Isabelle2013-1-RC1 instead of succeeding with try0 *)
  qed
  also have "\<dots> = (\<Sum> m \<in> N - {n} . b m (if m \<in> Range (winning_allocation_rel G N t b) then the_elem (((winning_allocation_rel G N t b)\<inverse>) `` {m}) else {}))" by simp
  also have "\<dots> = (\<Sum> m \<in> (N - {n}) \<inter> Range (winning_allocation_rel G N t b) . b m (the_elem (((winning_allocation_rel G N t b)\<inverse>) `` {m})))"
  proof -
    have "finite (N - {n})" using valid_input by (rule finite_participants_except)
    moreover have "\<forall> m \<in> N - {n} . b m {} = 0" (* CL: Sledgehammer of Isabelle2013-1-RC3 doesn't find anything here. *)
    proof -
      from valid_input have "\<forall> m \<in> N . b m {} = 0" unfolding valid_input_def CombinatorialAuction.valid_input_def by fastforce
      then show ?thesis by fastforce
    qed
    ultimately show ?thesis by (rule setsum_restrict_fun_zero')
  qed
  also have "\<dots> = (\<Sum> m \<in> (N - {n}) \<inter> Range (winning_allocation_rel G N t b) . b m (THE y . (y, m) \<in> winning_allocation_rel G N t b))"
  proof -
    {
      fix m
      assume "m \<in> (N - {n}) \<inter> Range (winning_allocation_rel G N t b)"
      then have "m \<in> Range (winning_allocation_rel G N t b)" by fast
      with runiq_alloc_conv have "the_elem (((winning_allocation_rel G N t b)\<inverse>) `` {m}) = (THE y . (y, m) \<in> winning_allocation_rel G N t b)"
        by (rule runiq_conv_imp_singleton_preimage')
      then have "b m (the_elem (((winning_allocation_rel G N t b)\<inverse>) `` {m})) = b m (THE y . (y, m) \<in> winning_allocation_rel G N t b)"
        by presburger
    }
    then have "\<forall> m \<in> (N - {n}) \<inter> Range (winning_allocation_rel G N t b) . b m (the_elem (((winning_allocation_rel G N t b)\<inverse>) `` {m}))
      = b m (THE y . (y, m) \<in> winning_allocation_rel G N t b)" by blast
    then show ?thesis by (rule setsum_cong2')
  qed
  also have "\<dots> = (\<Sum> m \<in> Range (winning_allocation_except G N t b n) . b m (THE y . (y, m) \<in> winning_allocation_rel G N t b))"
    using alloc_except_Range by presburger
  also have "\<dots> = (\<Sum> m \<in> Range (winning_allocation_except G N t b n) . b m (THE y . (y, m) \<in> winning_allocation_except G N t b n))"
  proof (rule setsum_cong2)
    fix m
    assume m_Range: "m \<in> Range (winning_allocation_except G N t b n)"
    then have "\<forall> y . (y, m) \<in> winning_allocation_rel G N t b \<longleftrightarrow> (y, m) \<in> (winning_allocation_except G N t b n)"
      using alloc_except_Range by simp
      (* CL: "try" in Isabelle2013-1-RC3 doesn't give preference to "try0" *)
    then show "b m (THE y . (y, m) \<in> winning_allocation_rel G N t b) = b m (THE y . (y, m) \<in> winning_allocation_except G N t b n)"
      by presburger
  qed
  also have "\<dots> = (\<Sum> y \<in> Domain (winning_allocation_except G N t b n) . b (THE m . (y, m) \<in> winning_allocation_except G N t b n) y)"
    using alloc_except_runiq alloc_except_conv_runiq
    unfolding winning_allocation_except.simps
    by (rule setsum_Domain_Range_runiq_rel[symmetric])
  also have "\<dots> = (\<Sum> y \<in> Domain (winning_allocation_except G N t b n) . b ((winning_allocation_except G N t b n) ,, y) y)"
  proof -
    {
      fix y
      assume "y \<in> Domain (winning_allocation_except G N t b n)"
      with alloc_except_runiq
        have "(THE m . (y, m) \<in> winning_allocation_except G N t b n) = the_elem ((winning_allocation_except G N t b n) `` {y})"
        unfolding winning_allocation_except.simps
        by (rule runiq_imp_singleton_image'[symmetric])
      also have "\<dots> = (winning_allocation_except G N t b n) ,, y" by simp
      finally have "(THE m . (y, m) \<in> winning_allocation_except G N t b n) = (winning_allocation_except G N t b n) ,, y" .
    }
    then show ?thesis by auto
  qed
  also have "\<dots> = value_rel b (winning_allocation_except G N t b n)" by simp
  finally show ?thesis .
qed

text {* The combinatorial Vickrey auction is well-defined. *}
lemma wd_outcome:
  fixes t::tie_breaker_rel
  assumes "tie_breaker t"
  shows "wd_outcome (nVCG_auctions t) valid_input wd_alloc_pay"
proof (rule wd_outcomeI)
  fix G N b x p
  assume "((G, N, b), (x, p)) \<in> nVCG_auctions t"
  then have xp: "x = winning_allocation_rel G N t b \<and> p = payments_rel G N t b" by (rule split_outcome)
  then have x': "x = winning_allocation_rel G N t b" by fast

  assume valid: "valid_input G N b"
  with x' assms obtain Y where part: "Y \<in> all_partitions G" and inj: "x \<in> injections Y N"
    using winning_allocation_injective by blast
  from valid have "finite G" by (rule finite_goods)

  (* TODO CL: get rid of redundancy with beginning of proof of lemma remaining_value_alt *)
  from inj have runiq_alloc: "runiq x" unfolding injections_def by simp
  from inj have runiq_alloc_conv: "runiq (x\<inverse>)" unfolding injections_def by simp
  from inj have alloc_Domain: "Domain x = Y" unfolding injections_def by simp
  from inj have alloc_Range: "Range x \<subseteq> N" unfolding injections_def by simp

  from part have "is_partition_of Y G" unfolding all_partitions_def by (rule CollectD)
  moreover have "Domain x = Y" using inj unfolding injections_def by simp
  ultimately have "is_partition_of (Domain x) G" by blast

  from xp (* to use Max_in, we need additional assumptions about N and G, so that \<Union> is non-empty *)
    have p_unfolded: "p = (\<lambda>n . (Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))))
      - remaining_value_rel G N t b n)" by fastforce

  have "wd_allocation G N x"
  proof -
    have "no_good_allocated_twice G x" unfolding no_good_allocated_twice_def
    proof
      fix g assume "g \<in> G"
      from inj have "runiq x" unfolding injections_def by simp
      moreover have "trivial { X \<in> Domain x . g \<in> X }"
      proof -
        from `g \<in> G` `is_partition_of (Domain x) G`
          have "\<exists>! X \<in> Domain x . g \<in> X" by (rule elem_in_uniq_eq_class)
        then show ?thesis by (rule ex1_imp_trivial)
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
    from valid have "finite (N - {n})" by (rule finite_participants_except)

    from p_unfolded have "p n = (Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))))
      - remaining_value_rel G N t b n" by fast
    also have "\<dots> = (Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))))
      - value_rel b (winning_allocation_except G N t b n)" 
      using valid assms by (metis (lifting, no_types) remaining_value_alt)
    finally have "p n = (Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))))
      - value_rel b (winning_allocation_except G N t b n)" .
    moreover have "Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))) \<ge> value_rel b (winning_allocation_except G N t b n)"
    proof cases
      assume "n \<in> Range x"
      have "Max ((value_rel b) ` (possible_allocations_rel G (N - {n})))
        (* If you (re-)allocate, to all participants except n,
           the goods except those that participant n gets in the winning allocation,
           you achieve at most the value you'd achieve when allocating everything.
           If participant n got nothing, \<ge> still holds, with equality. *)
        \<ge> Max ((value_rel b) ` (possible_allocations_rel (G - (THE y . (y, n) \<in> x)) (N - {n})))" sorry
      also have "Max ((value_rel b) ` (possible_allocations_rel (G - (THE y . (y, n) \<in> x)) (N - {n})))
        (* The LHS of this inequality asks for the maximum value of an allocation of all goods
           except those that n gets, when allocated to all participants except n.
           The RHS asks for the value of _one_ allocation of all goods except those that n gets
           to all participants except n (as it removes exactly these pairs of the winning 
           allocation of all goods to all participants), so it must be \<le> the LHS. *)
        \<ge> value_rel b (winning_allocation_except G N t b n)"
      proof (rule Max_fun_ge)
        show "finite (possible_allocations_rel (G - (THE y . (y, n) \<in> x)) (N - {n}))"
        proof (rule allocs_finite)
          from `finite G` show "finite (G - (THE y . (y, n) \<in> x))" by (rule finite_Diff)
          from `finite (N - {n})` show "finite (N - {n})" . (* TODO CL: find out how to abbreviate this *)
        qed
        show "winning_allocation_except G N t b n \<in> possible_allocations_rel (G - (THE y . (y, n) \<in> x)) (N - {n})"
        proof -
          from runiq_alloc winning_allocation_except_subrel have alloc_except_runiq: "runiq (winning_allocation_except G N t b n)" unfolding x' by (rule subrel_runiq)
          from winning_allocation_except_subrel have "(winning_allocation_except G N t b n)\<inverse> \<subseteq> (winning_allocation_rel G N t b)\<inverse>" by fastforce
          with runiq_alloc_conv have alloc_except_conv_runiq: "runiq ((winning_allocation_except G N t b n)\<inverse>)" unfolding x' by (rule subrel_runiq)
          have alloc_except_Domain: "Domain (winning_allocation_except G N t b n) \<in> all_partitions (G - (THE y . (y, n) \<in> x))"
          proof -
            have "winning_allocation_except G N t b n = { (y::goods, m::participant) .
              (y::goods, m::participant) \<in> x \<and> m \<noteq> n }" unfolding x' by simp
            have "\<Union> (Domain (winning_allocation_except G N t b n)) = G - (THE y . (y, n) \<in> x)"
            proof -
              have "Y - { THE y . (y, n) \<in> x } = Domain { (y, m) . (y, m) \<in> x \<and> m \<noteq> n }"
              proof -
                (* have \<dots> moreover have \<dots> ultimately have \<dots> also have \<dots> finally have \<dots>
                   wouldn't work; Isabelle would complain about a "vacuous calculation result". *)
                from runiq_alloc runiq_alloc_conv `n \<in> Range x`
                  have "{ (y, m) . (y, m) \<in> x \<and> m \<noteq> n } = { (y, m) . (y, m) \<in> x \<and> y \<noteq> (THE y . (y, n) \<in> x) }"
                  by (rule runiq_relation_except_singleton[symmetric])
                moreover have "Domain { (y, m) . (y, m) \<in> x \<and> y \<noteq> (THE y . (y, n) \<in> x) }
                    = Y - { THE y . (y, n) \<in> x }"
                  using alloc_Domain
                  by (auto simp add: Domain_except)
                ultimately show ?thesis by presburger
              qed
              also have "\<dots> = Domain (winning_allocation_except G N t b n)" unfolding x' by simp
              finally have Dom_Y: "Y - { THE y . (y, n) \<in> x } = Domain (winning_allocation_except G N t b n)" .

              show ?thesis
              proof
                {
                  fix g
                  assume "\<exists> A \<in> Domain (winning_allocation_except G N t b n) . g \<in> A"
                  then obtain A where "g \<in> A" and *: "A \<in> Domain (winning_allocation_except G N t b n)" by blast
                  from * have A_in_Y: "A \<in> Y - { THE y . (y, n) \<in> x }" using Dom_Y by presburger
                  have "g \<in> G - (THE y . (y, n) \<in> x)"
                  proof -
                    from A_in_Y have "A \<in> Y" by fast
                    with `g \<in> A` have "g \<in> G"
                      using part unfolding all_partitions_def by (auto simp add: is_partition_of_def)
                    have "g \<notin> (THE y . (y, n) \<in> x)"
                    proof
                      assume "g \<in> (THE y . (y, n) \<in> x)" (* Assume that g is one of the goods that n gets. *)
                      from alloc_Domain `n \<in> Range x` runiq_alloc runiq_alloc_conv
                        have *: "(THE y . (y, n) \<in> x) \<in> Y" 
                        by (metis Domain_iff Range.simps runiq_conv_imp_THE_left_comp)
                      from part have "is_partition_of Y G" unfolding all_partitions_def ..
                      with `g \<in> G`
                           `g \<in> (THE y . (y, n) \<in> x)` `(THE y . (y, n) \<in> x) \<in> Y` (* g in one equivalence class *)
                           `g \<in> A` `A \<in> Y` (* g in another equivalence class *)
                        have "A = (THE y . (y, n) \<in> x)" (* \<Rightarrow> both equivalence classes are equal *)
                        using elem_in_uniq_eq_class by smt
                      with A_in_Y show False by fast
                    qed
                    with `g \<in> G` show ?thesis by (rule DiffI)
                  qed
                }
                then show "\<Union> (Domain (winning_allocation_except G N t b n)) \<subseteq> G - (THE y . (y, n) \<in> x)" by auto
              next
                {
                  fix g
                  assume "g \<in> G - (THE y . (y, n) \<in> x)" (* Let g be one of the goods that n doesn't get. *)
                  moreover have "is_partition_of Y G" using part unfolding all_partitions_def ..
                  ultimately have "\<exists> A \<in> Y - { THE y . (y, n) \<in> x } . g \<in> A" by (rule diff_elem_in_eq_class)
                  with Dom_Y have "\<exists> A \<in> Domain (winning_allocation_except G N t b n) . g \<in> A" by presburger
                }
                then show "G - (THE y . (y, n) \<in> x) \<subseteq> \<Union> (Domain (winning_allocation_except G N t b n))" by fast
              qed
            qed
            moreover have "is_partition (Domain (winning_allocation_except G N t b n))"
            proof -
              {
                fix X Y
                assume X_Dom: "X \<in> Domain (winning_allocation_except G N t b n)"
                assume Y_Dom: "Y \<in> Domain (winning_allocation_except G N t b n)"
                from X_Dom have X_Dom': "X \<in> Domain x" unfolding x' by auto
                from Y_Dom have Y_Dom': "Y \<in> Domain x" unfolding x' by auto
                from part alloc_Domain have "Domain x \<in> all_partitions G" by simp
                then have "is_partition (Domain x)" unfolding all_partitions_def is_partition_of_def by fast
                then have "X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y" by (metis X_Dom' Y_Dom' is_partition_def)
              }
              then show ?thesis by (simp add: is_partition_def)
            qed
            ultimately have "is_partition_of (Domain (winning_allocation_except G N t b n)) (G - (THE y . (y, n) \<in> x))"
              unfolding is_partition_of_def by fast
            then show ?thesis unfolding all_partitions_def by (rule CollectI)
          qed
          from alloc_Range have "Range (winning_allocation_except G N t b n)
            = (N - {n}) \<inter> Range x"
            unfolding winning_allocation_except.simps x' by (rule Range_except)
          also have "\<dots> \<subseteq> N - {n}" by fast
          finally have alloc_except_Range: "Range (winning_allocation_except G N t b n) \<subseteq> N - {n}" .
          
          from alloc_except_Domain alloc_except_Range alloc_except_runiq alloc_except_conv_runiq
            obtain Y' where "Y' \<in> all_partitions (G - (THE y . (y, n) \<in> x))" and "winning_allocation_except G N t b n \<in> injections Y' (N - {n})"
            unfolding injections_def by blast
          then show ?thesis
            unfolding possible_allocations_rel.simps (* This allows for using blast; otherwise we'd need auto. *)
            by blast
        qed
      qed
      ultimately show ?thesis by linarith
    next
      assume "n \<notin> Range x"
      have "winning_allocation_except G N t b n = { (y::goods, m::participant) .
        (y::goods, m::participant) \<in> x \<and> m \<noteq> n }" unfolding x' by simp
      also have "\<dots> = x" using `n \<notin> Range x` by (rule Range_except_irrelevant)
      finally have x'': "winning_allocation_except G N t b n = x" .

      have finite: "finite (possible_allocations_rel G (N - {n}))"
        using `finite G` `finite (N - {n})` by (rule allocs_finite)

      note alloc_Domain
      moreover have "Range x \<subseteq> N - {n}" using alloc_Range `n \<notin> Range x` by fast
      moreover note runiq_alloc
      moreover note runiq_alloc_conv
      ultimately have "x \<in> injections Y (N - {n})" by (rule injectionsI)
      with part have "winning_allocation_except G N t b n \<in> possible_allocations_rel G (N - {n})"
        unfolding x'' possible_allocations_rel.simps (* This allows for using blast; otherwise we'd need auto. *)
        by blast
      with finite show ?thesis by (rule Max_fun_ge)
    qed
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

