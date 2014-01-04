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

(* TODO CL: document *)
lemma card_participants_except_gt_0:
  assumes "valid_input G N b"
  shows "card (N - {n}) > 0"
proof (cases "n \<in> N")
  case True
  have "finite (N - {n})" using assms by (rule finite_participants_except)
  moreover have "N - {n} \<noteq> {}"
  (* Sledgehammer in Isabelle2013-1-RC3 can't prove this within reasonable time. *)
  proof -
    have "card N > 1" using assms unfolding valid_input_def by fast
    moreover have "finite N" using assms by (rule finite_participants)
    ultimately show ?thesis using True by (smt card_Suc_Diff1 card_empty)
  qed
  ultimately show ?thesis by fastforce
next
  case False
  then have "N - {n} = N" by simp
  then show ?thesis by (metis assms card_participants_gt_0)
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

    from `card G > 0` `card N > 0`
      have "possible_allocations_rel G N \<noteq> {}"
      by (rule ex_allocations)
    moreover have "finite (possible_allocations_rel G N)"
      using `finite G` `finite N` by (rule allocs_finite)
    ultimately have "arg_max' (value_rel b) (possible_allocations_rel G N) \<noteq> {}"
      by (rule arg_max'_non_empty_iff)
    then show ?thesis by fast
  qed
  with tie_breaker alloc_unfolded
    have "winning_allocation_rel G N t b \<in> arg_max' (value_rel b) (possible_allocations_rel G N)"
    using tie_breaker_def by smt
  then have "winning_allocation_rel G N t b \<in> { x \<in> possible_allocations_rel G N .
    value_rel b x = Max ((value_rel b) ` (possible_allocations_rel G N)) }" by force
  then have "winning_allocation_rel G N t b \<in> possible_allocations_rel G N
    \<and> value_rel b (winning_allocation_rel G N t b) = Max ((value_rel b) ` (possible_allocations_rel G N))"
    by (rule CollectD)
  then have "winning_allocation_rel G N t b \<in> possible_allocations_rel G N" ..
  then show ?thesis using that by (rule allocation_injective)
qed

text {* determine the winning allocation, but take out the tuple of participant @{term n} *}
fun winning_allocation_except
where "winning_allocation_except G N t b n = { (y::goods, m::participant) .
  (y, m) \<in> winning_allocation_rel G N t b \<and> m \<noteq> n }"

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
  from inj have runiq_alloc: "runiq (winning_allocation_rel G N t b)"
            and runiq_alloc_conv: "runiq ((winning_allocation_rel G N t b)\<inverse>)"
            and alloc_Range: "Range (winning_allocation_rel G N t b) \<subseteq> N" unfolding injections_def by simp_all

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

(* TODO CL: once done, factor out parts into lemmas *)
text {* The combinatorial Vickrey auction is well-defined. *}
lemma wd_outcome:
  fixes t::tie_breaker_rel
  assumes "tie_breaker t"
  shows "wd_outcome (nVCG_auctions t) valid_input wd_alloc_pay"
proof (rule wd_outcomeI)
  fix G N b x p
  assume "((G, N, b), (x, p)) \<in> nVCG_auctions t"
  (* isolate the outcome of the auction (given in relational form) *)
  then have xp: "x = winning_allocation_rel G N t b \<and> p = payments_rel G N t b" by (rule split_outcome)
  then have x': "x = winning_allocation_rel G N t b" by fast

  (* As we are doing the overall proof by rule wd_outcomeI, we need to show
     wd_alloc_pay G N b x p
     under the following assumption: *)
  assume valid: "valid_input G N b"
  with x' assms obtain Y where part: "Y \<in> all_partitions G" and inj: "x \<in> injections Y N"
    using winning_allocation_injective by blast
  from valid have "finite G" by (rule finite_goods)

  (* TODO CL: get rid of redundancy with beginning of proof of lemma remaining_value_alt *)
  (* properties of the winning allocation x being an injective functional relation: *)
  from inj have runiq_alloc: "runiq x"
            and runiq_alloc_conv: "runiq (x\<inverse>)"
            and alloc_Domain: "Domain x = Y"
            and alloc_Range: "Range x \<subseteq> N" unfolding injections_def by simp_all

  from part have part': "is_partition_of Y G" unfolding all_partitions_def by (rule CollectD)
  with alloc_Domain have "is_partition_of (Domain x) G" by blast

 (* TODO CL: figure out what to do with the following comment, which seems useful but
    has never quite belonged _here_:
    To take advantage of Big_Operators.Max_in (* finite ?A \<Longrightarrow> ?A \<noteq> {} \<Longrightarrow> Max ?A \<in> ?A *),
    we need additional assumptions about N and G,
    so that the \<Union>, which possible_allocations_rel is defined to be, ends up non-empty. *)

  from xp
    have p_unfolded: "p = (\<lambda>n . (Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))))
      - remaining_value_rel G N t b n)" by fastforce

  (* the first aspect of a well-defined outcome: the allocation is well-defined: *)
  have "wd_allocation G N x"
  proof -
    (* 1. No good is allocated twice. *)
    have "no_good_allocated_twice G x" unfolding no_good_allocated_twice_def
    proof
      fix g assume "g \<in> G"
      note `runiq x`
      moreover have "trivial { X \<in> Domain x . g \<in> X }"
      proof -
        from `g \<in> G` `is_partition_of (Domain x) G`
          have "\<exists>! X \<in> Domain x . g \<in> X" by (rule elem_in_uniq_eq_class)
        then show ?thesis by (rule ex1_imp_trivial)
      qed
      ultimately show "trivial (x `` { P \<in> Domain x . g \<in> P })" by (auto simp only: runiq_def)
    qed
    (* 2. We only allocate goods we have. *)
    moreover have "\<Union> Domain x \<subseteq> G" using `is_partition_of (Domain x) G` unfolding is_partition_of_def by blast
    (* 3. We only allocate to participants of the auction. *)
    moreover note `Range x \<subseteq> N`
    ultimately show ?thesis unfolding wd_allocation_def by blast
  qed
  (* the second aspect of a well-defined outcome: the payments are well-defined: *)
  moreover have "wd_payments N p" unfolding wd_payments_def
  proof
    fix n assume "n \<in> N" (* For any such participant, we need to show "p n \<ge> 0". *)
    let ?n's_goods = "THE y . (y, n) \<in> x" (* the goods that participant n gets in the winning allocation x *)
    (* TODO CL: find out how to abbreviate "from `X` show X ." *)

    (* establishing some properties about the finiteness and cardinality of the
       set of all participants except n and of some other sets derived from it: *)
    have "finite (G - ?n's_goods)" using `finite G` by (rule finite_Diff)
    moreover have "finite (N - {n})" using valid by (rule finite_participants_except)
    ultimately have "finite (possible_allocations_rel (G - ?n's_goods) (N - {n}))" by (rule allocs_finite)
    have "finite (possible_allocations_rel G (N - {n}))" using `finite G` `finite (N - {n})` by (rule allocs_finite)
    have "card (N - {n}) > 0" using valid by (rule card_participants_except_gt_0)

    from valid have monotonic_bids: "\<forall> n H H' . n \<in> N \<and> H \<subseteq> H' \<longrightarrow> b n H \<le> b n H'"
      and non_neg_bids: "\<forall> n H . n \<in> N \<and> H \<subseteq> G \<longrightarrow> b n H \<ge> 0"
      unfolding valid_input_def CombinatorialAuction.valid_input_def by simp_all

    (* We rewrite "p n" into a form that makes it easier to tell something about its
       non-negativeness: *)
    from p_unfolded have "p n = Max ((value_rel b) ` (possible_allocations_rel G (N - {n})))
      - remaining_value_rel G N t b n" by fast
    also have "\<dots> = Max ((value_rel b) ` (possible_allocations_rel G (N - {n})))
      - value_rel b (winning_allocation_except G N t b n)" 
      using valid assms by (metis (lifting, no_types) remaining_value_alt)
    finally have "p n = Max ((value_rel b) ` (possible_allocations_rel G (N - {n})))
      - value_rel b (winning_allocation_except G N t b n)" .
    moreover have "Max ((value_rel b) ` (possible_allocations_rel G (N - {n}))) \<ge> value_rel b (winning_allocation_except G N t b n)"
    (* The maximum value (always: according to bids) of an allocation of the goods to all participants except n,
       is \<ge> the value of the allocation that wins the auction of the goods to all participants
       (excluding the goods that this allocation would have allocated to participant n). *)
    (* Proof strategy: multi-level case distinction.  Identify easy cases, prove them first. *)
    proof cases
      (* This is the hard case.  The other one is easier. *)
      assume n_gets_something: "n \<in> Range x" (* note x': "x = winning_allocation_rel G N t b" *)
      (* The same, expressed in terms of goods: *)
      have n_gets_some_goods: "?n's_goods \<in> Domain x"
        using n_gets_something runiq_alloc_conv
        by (rule runiq_conv_imp_Range_rel_Dom)
      show ?thesis
      proof cases
        (* This is the hard case.  The other one is easier. *)
        assume n_gets_part: "?n's_goods \<noteq> G" (* i.e. participant n gets some but not all goods *)

        (* We have to show that the maximum value of an allocation of the goods to all participants except n (=: a)
           is \<ge> the value of the winning allocation of the goods to all participants after removing n's goods (=: c).
           We do this by showing a \<ge> b \<ge> c, for
           b := the maximum value of an allocation of all goods except n's goods to all participants except n.
           *)
        (* 1. "a \<ge> b" *)
        have "Max ((value_rel b) ` (possible_allocations_rel G (N - {n})))
          (* If you (re-)allocate, to all participants except n,
             the goods except those that participant n gets in the winning allocation,
             you achieve at most the value you'd achieve when allocating everything.
             If participant n got nothing, \<ge> still holds, with equality; but note that because of 
             the assumption 'n \<in> Range x' we assume that n always got something. *)
          \<ge> Max ((value_rel b) ` (possible_allocations_rel (G - ?n's_goods) (N - {n})))"
        proof -
          (* Participant n gets a subset of the goods: *)
          have "\<Union> (Domain x) = G" using alloc_Domain part' unfolding is_partition_of_def by simp
          with n_gets_some_goods have n_gets_part': "?n's_goods \<subseteq> G" by (metis Sup_upper)

          (* After removing n's goods, there are still some left: *)
          have goods_Diff_non_empty: "G - ?n's_goods \<noteq> {}"
            using n_gets_part n_gets_part'
            by (smt Diff_empty double_diff subset_refl)

          (* Therefore, there is an allocation of all goods except n's goods to all participants except n: *)
          note `finite (possible_allocations_rel G (N - {n}))`
          moreover note `finite (possible_allocations_rel (G - ?n's_goods) (N - {n}))` (* TODO CL: give this a symbolic name *)
          moreover have "possible_allocations_rel (G - ?n's_goods) (N - {n}) \<noteq> {}"
          proof (rule ex_allocations)
            show "card (G - ?n's_goods) > 0"
            proof -
              note `finite (G - ?n's_goods)`
              moreover note goods_Diff_non_empty
              ultimately show ?thesis by (metis card_gt_0_iff)
            qed
            show "card (N - {n}) > 0" using `card (N - {n}) > 0` .
          qed
          moreover have "\<forall> y' \<in> possible_allocations_rel (G - ?n's_goods) (N - {n}) .
            \<exists> x' \<in> possible_allocations_rel G (N - {n}) .
              value_rel b x' \<ge> value_rel b y'"
            (* TODO CL: generalise this into a lemma value_mono *)
            (* For each allocation of all goods, except those that n actually gets, to all participants except n,
               there is an allocation of _all_ goods to these participants, whose value is higher.
               This is hard to prove. *)
          proof
            fix y'
            assume "y' \<in> possible_allocations_rel (G - ?n's_goods) (N - {n})"
            then obtain Y' where part': "Y' \<in> all_partitions (G - ?n's_goods)" and y'_inj: "y' \<in> injections Y' (N - {n})" using that by (rule allocation_injective)
            from y'_inj have y'_Domain: "Domain y' = Y'" 
                         and y'_Range: "Range y' \<subseteq> N - {n}" 
                         and y'_runiq: "runiq y'" 
                         and y'_conv_runiq: "runiq (y'\<inverse>)" unfolding injections_def by simp_all
            have "?n's_goods \<noteq> {}"
            proof -
              from n_gets_some_goods alloc_Domain have *: "?n's_goods \<in> Y" by simp
              have "is_partition Y" using part unfolding all_partitions_def is_partition_of_def by simp (* TODO CL: let's see if we can reuse this elsewhere *)
              then have "{} \<notin> Y" by (rule no_empty_eq_class)
              with * show ?thesis by fastforce
            qed

            (* We construct the allocation x', for which we'd like to prove that its value is higher than that of y',
               by allocating everything as in y' and allocating the leftover goods (i.e. those that n got in the winning allocation x)
               to an arbitrary participant m, which means enlarging the set of
               goods that m got so far by the additional goods.
               OK, not _quite_ an arbitrary participant:
               It's easier if we choose someone from "Range y'", i.e. someone who already got something in y'. *)
            def m \<equiv> "SOME m . m \<in> Range y'"
            let ?m's_goods_y' = "THE y . (y, m) \<in> y'"

            from part' have part'': "is_partition_of Y' (G - ?n's_goods)" unfolding all_partitions_def ..
            with goods_Diff_non_empty have "Y' \<noteq> {}" by (rule non_empty_imp_non_empty_partition)
            with y'_Domain have "Range y' \<noteq> {}" by fast
            then have "m \<in> Range y'" unfolding m_def by (metis ex_in_conv tfl_some)
            with y'_conv_runiq have "(?m's_goods_y', m) \<in> y'" by (rule runiq_conv_imp_THE_left_comp')

            def x' \<equiv> "y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}"

            (* Some properties of x': *)
            have "Domain (y' - {(?m's_goods_y', m)}) = Domain y' - {?m's_goods_y'}"
              using y'_runiq `(?m's_goods_y', m) \<in> y'` by (rule Domain_runiq_Diff_singleton)
            then have x'_Domain_wrt_y': "Domain x' = Y' - {?m's_goods_y'} \<union> {?n's_goods \<union> ?m's_goods_y'}"
              unfolding x'_def y'_Domain by simp

            (* 1. First we need to show that x' is indeed an allocation of all goods to all participants except n. *)
            have "x' \<in> possible_allocations_rel G (N - {n})"
            proof -

              (* 1. The domain of x' is a partition of all goods. *)
              have x'_Domain: "Domain x' \<in> all_partitions G"
              proof -
                (* 1. We first show "\<Union> Domain x' = G" but need to do the steps on this level as we'd like to reuse some of them below. *)
                note x'_Domain_wrt_y'
                moreover have Union_Domain_y': "\<Union> Y' = G - ?n's_goods" using part'' unfolding is_partition_of_def y'_Domain ..
                moreover note n_gets_part'
                moreover have m's_goods_Domain_y': "?m's_goods_y' \<in> Y'"
                  unfolding y'_Domain[symmetric] using `(THE y. (y, m) \<in> y', m) \<in> y'`  by (rule DomainI)
                ultimately have "\<Union> Domain x' = G" by (rule Union_family_grown_member)
                (* 2. We then show that the domain of x' is a partition. *)
                moreover have "is_partition (Domain x')"
                (* Domain x' partitions the goods as Domain y' does, except that those goods that
                   Domain y' doesn't cover (i.e. those that n got in the winning allocation x)
                   are added to the equivalence class of those goods that participant m gets.

                   We have shown above that Domain x' covers the whole set G of goods.

                   It remains to be shown that Domain x' is a partition, i.e. that all of its
                   members are mutually disjoint.  This is the case for all members "inherited" 
                   from Domain y'.  It remains to be shown that the one new equivalence class,
                   which equals the union of the goods that m got in y'
                                          and the goods that n got in x,
                   is disjoint from all other equivalence classes.  This is the case when none of 
                   the elements _newly_ added to the new equivalence class has been a member of the
                   previously partitioned set (all goods except n's in x), i.e. when 
                   (ClassAfterAddition - ClassBeforeAddition) \<inter> PreviouslyPartitionedSet = {}

                   TODO CL: factor parts out into a lemma in Partitions.thy.
                   *)
                proof -
                  {
                    fix X'' Y''
                    assume assm: "X'' \<in> Domain x' \<and> Y'' \<in> Domain x'"
                    then have X''x': "X'' \<in> Domain x'" and Y''x': "Y'' \<in> Domain x'" by simp_all

                    (* The cases FalseTrue and TrueFalse of the proof below are symmetric;
                       therefore we establish their common part here: *)
                    {
                      fix X'' Y''
                      assume assm: "X'' \<in> Domain x' \<and> Y'' \<in> Domain x'"
                      then have X''x': "X'' \<in> Domain x'" and Y''x': "Y'' \<in> Domain x'" by simp_all

                      assume FalseTrue: "X'' \<notin> Y' \<and> Y'' \<in> Y'"
                      then have X''Y': "X'' \<notin> Y'" and Y''Y': "Y'' \<in> Y'" by simp_all
                      then have X: "X'' = ?n's_goods \<union> ?m's_goods_y'" using X''x' x'_Domain_wrt_y' by simp
                      then have "?n's_goods \<subseteq> X''" by fast
                      moreover have "\<not> ?n's_goods \<subseteq> Y''"
                        using part' `?n's_goods \<noteq> {}` Y''Y' unfolding all_partitions_def is_partition_of_def 
                        by blast
                      ultimately have "X'' \<noteq> Y''" by blast
                      moreover have "X'' \<inter> Y''= {}"
                      proof -
                        have "?n's_goods \<inter> Y'' = {}" using Y''Y' Union_Domain_y' by (smt Diff_disjoint Int_Diff Sup_upper le_iff_inf) (* TODO CL: maybe optimise performance by manual proof (so far: 59 ms in Isabelle2013-2) *)
                        moreover have "?m's_goods_y' \<inter> Y'' = {}"
                        proof -
                          have "?m's_goods_y' \<in> Domain y'" using m's_goods_Domain_y' y'_Domain by simp
                          then have "?m's_goods_y' \<notin> Domain (y' - {(?m's_goods_y', m)})"
                            by (metis DiffD2 `Domain (y' - {(THE y. (y, m) \<in> y', m)}) = Domain y' - {THE y. (y, m) \<in> y'}` insertI1)
                          with `?n's_goods \<noteq> {}` have "?m's_goods_y' \<notin> Domain x'" using m's_goods_Domain_y' X X''Y'  `Domain (y' - {(THE y. (y, m) \<in> y', m)}) = Domain y' - {THE y. (y, m) \<in> y'}` x'_Domain_wrt_y' y'_Domain
                            by (smt Un_iff singleton_iff) (* TODO CL: This step is fast but not intuitive. *)
                          with Y''x' have "?m's_goods_y' \<noteq> Y''" by fast
                          with m's_goods_Domain_y' Y''Y' part'' show ?thesis unfolding is_partition_of_def is_partition_def by metis 
                        qed
                        ultimately show ?thesis using X by (smt UnE disjoint_iff_not_equal) (* TODO CL: maybe optimise performance by manual proof (so far: 44 ms in Isabelle2013-2) *)
                      qed
                      ultimately have "(X'' \<inter> Y'' \<noteq> {}) \<longleftrightarrow> (X'' = Y'')" by auto
                    }
                    note FalseTrueRule = this

                    have "(X'' \<inter> Y'' \<noteq> {}) \<longleftrightarrow> (X'' = Y'')"
                    proof (cases rule: case_split_2_times_2)
                      assume TrueTrue: "X'' \<in> Y' \<and> Y'' \<in> Y'"
                      with y'_Domain part' show ?thesis
                        unfolding all_partitions_def is_partition_of_def is_partition_def by simp
                    next
                      assume FalseTrue: "X'' \<notin> Y' \<and> Y'' \<in> Y'"
                      with assm show ?thesis by (rule FalseTrueRule)
                    next
                      assume TrueFalse: "X'' \<in> Y' \<and> Y'' \<notin> Y'"
                      (* symmetric to case FalseTrue *)
                      from assm have "Y'' \<in> Domain x' \<and> X'' \<in> Domain x'" by simp
                      moreover have "Y'' \<notin> Y' \<and> X'' \<in> Y'" using TrueFalse by simp
                      ultimately have "(Y'' \<inter> X'' \<noteq> {}) \<longleftrightarrow> (Y'' = X'')" by (rule FalseTrueRule)
                      then show ?thesis by blast
                    next
                      assume FalseFalse: "X'' \<notin> Y' \<and> Y'' \<notin> Y'"
                      then have X''Y': "X'' \<notin> Y'" and Y''Y': "Y'' \<notin> Y'" by simp_all

                      have "X'' = ?n's_goods \<union> ?m's_goods_y'" using X''x' x'_Domain_wrt_y' X''Y' by simp
                      moreover have "Y'' = ?n's_goods \<union> ?m's_goods_y'" using Y''x' x'_Domain_wrt_y' Y''Y' by simp
                      ultimately have "X'' = Y''" by force
                      moreover have "X'' \<inter> Y'' \<noteq> {}"
                      proof -
                        from `?n's_goods \<noteq> {}` have "?n's_goods \<union> ?m's_goods_y' \<noteq> {}" by fast
                        with `X'' = ?n's_goods \<union> ?m's_goods_y'` `X'' = Y''` show ?thesis by blast
                      qed
                      ultimately show ?thesis by force
                    qed
                  }
                  then show ?thesis unfolding is_partition_def by simp
                qed
                ultimately show ?thesis unfolding all_partitions_def is_partition_of_def by fast
              qed
              (* 2. The range of x' is a subset of the set of all participants except n. *)
              have x'_Range: "Range x' \<subseteq> N - {n}"
              proof -
                have "Range x' = Range y'" unfolding x'_def using `(?m's_goods_y', m) \<in> y'` by auto
                with y'_Range show ?thesis by presburger
              qed
              (* 3. x' is a right-unique relation. *)
              have x'_runiq: "runiq x'"
                unfolding x'_def
                using y'_runiq
              proof (rule runiq_replace_fst)
                show "?n's_goods \<union> ?m's_goods_y' \<notin> Domain y'"
                proof (rule ccontr)
                  assume "\<not> ?n's_goods \<union> ?m's_goods_y' \<notin> Domain y'"
                  then have "?n's_goods \<union> ?m's_goods_y' \<in> Domain y'" by fast
                  then have "?n's_goods \<subseteq> \<Union> (Domain y')"
                  proof -
                    have "{g. g \<in> ?n's_goods \<or> g \<in> ?m's_goods_y'} \<in> Domain y'"
                      by (metis Un_def `?n's_goods \<union> ?m's_goods_y' \<in> Domain y'`)
                    then show ?thesis by auto
                  qed
                  moreover have *: "\<Union> (Domain y') = G - ?n's_goods"
                    using y'_Domain part''
                    unfolding is_partition_of_def by fast
                  ultimately show False using `?n's_goods \<noteq> {}` by blast
                qed
              qed
              (* 4. The converse relation of x' is also right-unique.*)
              have x'_conv_runiq: "runiq (x'\<inverse>)"
                unfolding x'_def
                (* x'_def is simply formed from y' by replacing the first component of one pair. *)
                using y'_conv_runiq `(?m's_goods_y', m) \<in> y'`
                by (rule runiq_conv_replace_fst')
              (* Therefore, x' is an allocation of all goods to all participants except n. *)
              from x'_Domain x'_Range x'_runiq x'_conv_runiq show ?thesis unfolding possible_allocations_rel.simps injections_def by blast
            qed
            (* 2. After having shown that x' is an allocation of all goods to all participants except n,
                  we need to show that its value is higher than that of y'. *)
            moreover have "value_rel b x' \<ge> value_rel b y'"
            proof -
              have "value_rel b x' = (\<Sum> (y::goods) \<in> Domain x' . b (x' ,, y) y)" by simp
              also have "\<dots> = (\<Sum> (y::goods) \<in> Y' - {?m's_goods_y'} \<union> {?n's_goods \<union> ?m's_goods_y'} . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)"
                using x'_Domain_wrt_y'
                unfolding x'_def
                by presburger
              also have "\<dots> = (\<Sum> y \<in> Y' . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                - (\<Sum> y \<in> {?m's_goods_y'} . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                + (\<Sum> y \<in> {?n's_goods \<union> ?m's_goods_y'} . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)"
              proof (rule setsum_diff_union)
                (* TODO CL: By factoring things out of step 1 above (x' is an allocation),
                   we should get most of the following for free: *)
                show "finite Y'" sorry
                show "{?m's_goods_y'} \<subseteq> Y'" sorry
                show "finite {?n's_goods \<union> ?m's_goods_y'}" sorry
                show "(Y' - {?m's_goods_y'}) \<inter> {?n's_goods \<union> ?m's_goods_y'} = {}" sorry
              qed
              also have "\<dots> = (\<Sum> y \<in> Y' . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                - b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, ?m's_goods_y') ?m's_goods_y' (* = 0 because in x' ?m's_goods_y' are in a package together with ?n's_goods, which is \<noteq> {} *)
                + b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, (?n's_goods \<union> ?m's_goods_y')) (?n's_goods \<union> ?m's_goods_y')" by force
              (* We remove the 2nd summand as it is 0: *)
              also have "\<dots> = (\<Sum> y \<in> Y' . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                + b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, (?n's_goods \<union> ?m's_goods_y')) (?n's_goods \<union> ?m's_goods_y')" sorry
              (* We evaluate the relation in the 2nd summand: *)
              also have "\<dots> = (\<Sum> y \<in> Y' . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                + b m (?n's_goods \<union> ?m's_goods_y')" sorry
              (* We make the 2nd summand smaller thanks to the monotonicity requirement: *)
              also have "\<dots> \<ge> (\<Sum> y \<in> Y' . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                + b m ?m's_goods_y'" sorry
              (* We need to end this chain here, as continuing would give us the error message "vacuous calculation result" *)
              finally have "value_rel b x' \<ge> 
                (\<Sum> y \<in> Y' . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                + b m ?m's_goods_y'" .
              (* As bids are non-negative, we make a sum smaller by removing elements from the set to be summed over: *)
              moreover have "\<dots> \<ge> (\<Sum> y \<in> Y' - {?m's_goods_y'} . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                + b m ?m's_goods_y'" sorry
              ultimately have "value_rel b x' \<ge> (\<Sum> y \<in> Y' - {?m's_goods_y'} . b ((y' - {(?m's_goods_y', m)} \<union> {(?n's_goods \<union> ?m's_goods_y', m)}) ,, y) y)
                + b m ?m's_goods_y'" by fast
              (* Neither ?m's_goods_y' nor ?n's_goods are in Y' - {?m's_goods_y'}, so removing them from the relation in the 1st summand doesn't change what it evaluates to on that set: *)
              (* also *) have "\<dots> = (\<Sum> y \<in> Y' - {?m's_goods_y'} . b (y' ,, y) y)
                + b m ?m's_goods_y'" sorry
              also have "\<dots> = (\<Sum> y \<in> Y' - {?m's_goods_y'} . b (y' ,, y) y)
                + b (y' ,, ?m's_goods_y') ?m's_goods_y'" sorry
              (* We put the sums together (using some setsum_* lemma) *)
              also have "\<dots> = (\<Sum> y \<in> Y' . b (y' ,, y) y)" sorry
              also have "\<dots> = (\<Sum> y \<in> Domain y' . b (y' ,, y) y)" unfolding y'_Domain ..
              also have "\<dots> = value_rel b y'" by simp
              finally show ?thesis by linarith
            qed
            ultimately show "\<exists> x' \<in> possible_allocations_rel G (N - {n}) . value_rel b x' \<ge> value_rel b y'" by blast
          qed
          ultimately show ?thesis by (rule Max_Im_ge_other_Im)
        qed
        (* 2. "b \<ge> c" *)
        also have "Max ((value_rel b) ` (possible_allocations_rel (G - ?n's_goods) (N - {n})))
          (* The LHS of this inequality asks for the maximum value of an allocation of all goods
             except those that n gets, when allocated to all participants except n.
             The RHS asks for the value of _one_ allocation of all goods except those that n gets
             to all participants except n (as it removes exactly these pairs of the winning 
             allocation of all goods to all participants), so it must be \<le> the LHS. *)
          \<ge> value_rel b (winning_allocation_except G N t b n)"
          using `finite (possible_allocations_rel (G - ?n's_goods) (N - {n}))` (* TODO CL: give this a symbolic name *)
        proof (rule Max_Im_ge)
          (* We need to show that the winning allocation of the goods to all participants, with n's goods removed,
             is one possible allocation of all goods except n's to all participants except n. *)

          (* 1. The relation is right-unique. *)
          from runiq_alloc winning_allocation_except_subrel have alloc_except_runiq: "runiq (winning_allocation_except G N t b n)" unfolding x' by (rule subrel_runiq)
          from winning_allocation_except_subrel have "(winning_allocation_except G N t b n)\<inverse> \<subseteq> (winning_allocation_rel G N t b)\<inverse>" by fastforce
          (* 2. Its converse is also right-unique. *)
          with runiq_alloc_conv have alloc_except_conv_runiq: "runiq ((winning_allocation_except G N t b n)\<inverse>)" unfolding x' by (rule subrel_runiq)

          (* 3. Its domain is a partition of the goods except n's. *)
          have alloc_except_Domain: "Domain (winning_allocation_except G N t b n) \<in> all_partitions (G - ?n's_goods)"
          proof -
            have "winning_allocation_except G N t b n = { (y::goods, m::participant) .
              (y::goods, m::participant) \<in> x \<and> m \<noteq> n }" unfolding x' by simp
            (* 1. The big union of the domain is the set of goods except n's. *)
            have "\<Union> (Domain (winning_allocation_except G N t b n)) = G - ?n's_goods"
            proof -
              (* We first show that the domain is the same as the partition of the set of all goods according to the winning allocation, minus the goods that n got there. *)
              have "Y - { ?n's_goods } = Domain { (y, m) . (y, m) \<in> x \<and> m \<noteq> n }"
              proof -
                (* have \<dots> moreover have \<dots> ultimately have \<dots> also have \<dots> finally have \<dots>
                   wouldn't work; Isabelle would complain about a "vacuous calculation result". *)
                from runiq_alloc runiq_alloc_conv n_gets_something
                  have "{ (y, m) . (y, m) \<in> x \<and> m \<noteq> n } = { (y, m) . (y, m) \<in> x \<and> y \<noteq> ?n's_goods }"
                  by (rule runiq_relation_except_singleton[symmetric])
                moreover have "Domain { (y, m) . (y, m) \<in> x \<and> y \<noteq> ?n's_goods }
                    = Y - { ?n's_goods }"
                  using alloc_Domain
                  by (auto simp add: Domain_except)
                ultimately show ?thesis by presburger
              qed
              also have "\<dots> = Domain (winning_allocation_except G N t b n)" unfolding x' by simp
              finally have Dom_Y: "Y - { ?n's_goods } = Domain (winning_allocation_except G N t b n)" .

              show ?thesis
              proof (* "\<subseteq>" *)
                {
                  fix g
                  assume "\<exists> A \<in> Domain (winning_allocation_except G N t b n) . g \<in> A"
                  then obtain A where "g \<in> A" and *: "A \<in> Domain (winning_allocation_except G N t b n)" by blast
                  from * have A_in_Y: "A \<in> Y - { ?n's_goods }" using Dom_Y by presburger
                  have "g \<in> G - ?n's_goods"
                  proof -
                    from A_in_Y have "A \<in> Y" by fast
                    with `g \<in> A` have "g \<in> G"
                      using part unfolding all_partitions_def by (auto simp add: is_partition_of_def)
                    have "g \<notin> ?n's_goods"
                    proof
                      assume "g \<in> ?n's_goods" (* Assume that g is one of the goods that n gets. *)
                      from alloc_Domain n_gets_something runiq_alloc runiq_alloc_conv
                        have *: "?n's_goods \<in> Y" 
                        by (metis Domain_iff Range.simps runiq_conv_imp_THE_left_comp)
                      with `g \<in> G`
                           `g \<in> ?n's_goods` `?n's_goods \<in> Y` (* g in one equivalence class *)
                           `g \<in> A` `A \<in> Y` (* g in another equivalence class *)
                           part'
                        have "A = ?n's_goods" (* \<Rightarrow> both equivalence classes are equal *)
                        using elem_in_uniq_eq_class by smt
                      with A_in_Y show False by fast
                    qed
                    with `g \<in> G` show ?thesis by (rule DiffI)
                  qed
                }
                then show "\<Union> (Domain (winning_allocation_except G N t b n)) \<subseteq> G - ?n's_goods" by auto
                  (* Sledgehammer in Isabelle2013-2 can't prove this with default timeouts. *)
              next (* "\<subseteq>" *)
                {
                  fix g
                  assume "g \<in> G - ?n's_goods" (* Let g be one of the goods that n doesn't get. *)
                  moreover note part'
                  ultimately have "\<exists> A \<in> Y - { ?n's_goods } . g \<in> A" by (rule diff_elem_in_eq_class)
                  with Dom_Y have "\<exists> A \<in> Domain (winning_allocation_except G N t b n) . g \<in> A" by presburger
                }
                then show "G - ?n's_goods \<subseteq> \<Union> (Domain (winning_allocation_except G N t b n))" by fast
              qed
            qed
            (* 2. The domain is a partition. *)
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
            ultimately have "is_partition_of (Domain (winning_allocation_except G N t b n)) (G - ?n's_goods)"
              unfolding is_partition_of_def by fast
            then show ?thesis unfolding all_partitions_def by (rule CollectI)
          qed
          (* 4. The range of the relation is a subset of the participants except n. *)
          from alloc_Range have "Range (winning_allocation_except G N t b n)
            = (N - {n}) \<inter> Range x"
            unfolding winning_allocation_except.simps x' by (rule Range_except)
          also have "\<dots> \<subseteq> N - {n}" by fast
          finally have alloc_except_Range: "Range (winning_allocation_except G N t b n) \<subseteq> N - {n}" .
          
          from alloc_except_Domain alloc_except_Range alloc_except_runiq alloc_except_conv_runiq
            show "winning_allocation_except G N t b n \<in> possible_allocations_rel (G - ?n's_goods) (N - {n})"
            unfolding possible_allocations_rel.simps injections_def by blast
        qed
        ultimately show ?thesis by linarith (* a \<ge> b \<and> b \<ge> c \<longrightarrow> a \<ge> c *)
      next
        assume "\<not> ?n's_goods \<noteq> G" (* participant n gets everything *)
        then have n_gets_everything: "?n's_goods = G" by fast

        (* TODO CL: "try" on the following gives no result after an hour with Isabelle2013-1-RC3: *)
        (* with part' alloc_Domain have "{} = { (y, m) . (y, m) \<in> x \<and> m \<noteq> n }" unfolding is_partition_of_def is_partition_def *)
        (* OK, maybe I took into account too few assumptions.  TODO CL: retry with all assumptions actually used below. *)

        (* No sets of goods get allocated to participants other than n: *)
        have "{} = { (y, m) . (y, m) \<in> x \<and> m \<noteq> n }"
        proof (rule ccontr) (* TODO CL: clean up the following.  Intuitively it's clear anyway, but the formalisation needs to become more readable. *)
          assume "{} \<noteq> { (y, m) . (y, m) \<in> x \<and> m \<noteq> n }"
          then obtain y m where 0: "(y, m) \<in> x \<and> m \<noteq> n" by (smt empty_Collect_eq prod_caseE)
          with alloc_Domain have "y \<in> Y" by fast
          from `?n's_goods \<in> Domain x` have *: "?n's_goods \<in> Y" using alloc_Domain by simp
          with `y \<in> Y` part' have "\<Union> Y = G" unfolding is_partition_of_def is_partition_def by force
          from * `y \<in> Y` part' have "y \<inter> ?n's_goods \<noteq> {} \<longleftrightarrow> y = ?n's_goods" unfolding is_partition_of_def is_partition_def by force
          then have **: "y \<inter> G \<noteq> {} \<longleftrightarrow> y = G" unfolding n_gets_everything by fast
          from `y \<in> Y` `\<Union> Y = G` have "y \<subseteq> G" by fast
          with `y \<in> Y` have "y \<inter> G \<noteq> {}" by (metis inf.orderE is_partition_of_def no_empty_eq_class part')
          with ** have "y = G" by blast
          with 0 have "(G, m) \<in> x \<and> m \<noteq> n" by fastforce
          with n_gets_everything runiq_alloc runiq_alloc_conv
            show False
            by (metis Range_iff converse.simps converse_converse n_gets_something runiq_conv_wrt_THE) (* TODO CL: optimise *)
        qed
        also have "\<dots> = winning_allocation_except G N t b n" unfolding x' by simp
        (* Removing from the winning allocation the tuple of participant n leaves over nothing: *)
        finally have "{} = winning_allocation_except G N t b n" .
        then have Dom_empty: "Domain (winning_allocation_except G N t b n) = {}" by fast

        (* Therefore, the value of the allocation that wins the auction of the goods to all participants,
           excluding the goods that this allocation would have allocated to participant n,
           is 0. *)
        have "value_rel b (winning_allocation_except G N t b n) = 0"
          unfolding value_rel.simps Dom_empty by (rule setsum_empty)
        moreover have "0 \<le> Max (value_rel b ` possible_allocations_rel G (N - {n}))"
        (* We also show that the maximum value of an allocation of the goods to all participants except n
           is \<ge> 0. *)
        proof -
          (* 1. For any such allocation (if one exists), its value is \<ge> 0 *)
          have "\<forall> x' \<in> possible_allocations_rel G (N - {n}) . value_rel b x' \<ge> 0"
          proof
            fix x'
            assume "x' \<in> possible_allocations_rel G (N - {n})"
            then obtain Y' where Y': "Y' \<in> all_partitions G" and inj': "x' \<in> injections Y' (N - {n})"
              using that by (rule allocation_injective)
            from inj' have Dom_x': "Domain x' = Y'"
                       and Range_x': "Range x' \<subseteq> N - {n}"
                       and runiq_x': "runiq x'" unfolding injections_def by simp_all
            (* For any such allocation and any y that it allocates, this y is a set of available goods,
               and it gets allocated to one of the participants. *)
            (* TODO CL: Can this be factored out? *)
            {
              fix y
              assume "y \<in> Domain x'"
              with Dom_x' have 1: "y \<subseteq> G" using Y' all_partitions_def is_partition_of_def
                by (metis Union_upper mem_Collect_eq)
              from runiq_x' `y \<in> Domain x'` have "x' ,, y \<in> Range x'" by (rule eval_runiq_in_Range)
              with Range_x' have 2: "x' ,, y \<in> N" by blast
              from 1 2 have "y \<subseteq> G" and "x' ,, y \<in> N" .
            }
            (* Therefore, as we have a valid input of non-negative bids,
               the value of any such set of goods is non-negative, \<dots> *)
            with non_neg_bids have "\<forall> y \<in> Domain x' . b (x' ,, y) y \<ge> 0" by simp
            (* \<dots> and so is the value of their overall allocation. *)
            then show "value_rel b x' \<ge> 0" unfolding value_rel.simps by (rule setsum_nonneg)
          qed
          (* 2. There are finitely many such allocations. *)
          moreover note `finite (possible_allocations_rel G (N - {n}))`
          (* 3. There exists such an allocation. *)
          moreover have "possible_allocations_rel G (N - {n}) \<noteq> {}"
          proof (rule ex_allocations)
            from valid show "card G > 0" by (rule card_goods_gt_0)
            show "card (N - {n}) > 0" using `card (N - {n}) > 0` .
          qed
          ultimately show ?thesis by (rule Max_Im_ge_lower_bound)
        qed
        ultimately show ?thesis by (rule ord_eq_le_trans)
      qed
    next
      assume n_gets_nothing: "n \<notin> Range x" (* i.e. participant n gets nothing *)
      have "winning_allocation_except G N t b n = { (y::goods, m::participant) .
        (y::goods, m::participant) \<in> x \<and> m \<noteq> n }" unfolding x' by simp
      also have "\<dots> = x" using n_gets_nothing by (rule Range_except_irrelevant)
      (* As n gets nothing, removing its goods from the winning allocation doesn't change anything. *)
      finally have x'': "winning_allocation_except G N t b n = x" .

      (* Therefore, the winning allocation (with or without n's goods, which is the same)
         also is an allocation of all goods to all participants except n: *)
      note alloc_Domain
      moreover have "Range x \<subseteq> N - {n}" using alloc_Range n_gets_nothing by fast
      moreover note runiq_alloc runiq_alloc_conv
      ultimately have "x \<in> injections Y (N - {n})" by (rule injectionsI)
      with part have "winning_allocation_except G N t b n \<in> possible_allocations_rel G (N - {n})"
        unfolding x'' possible_allocations_rel.simps (* Unfolding allows for using blast; otherwise we'd need auto. *)
        by blast
      (* Therefore, the value of the winning allocation is \<le>
         the maximum value of all allocations of all goods to all participants except n: *)
      with `finite (possible_allocations_rel G (N - {n}))`
        show "value_rel b (winning_allocation_except G N t b n) \<le> Max (value_rel b ` possible_allocations_rel G (N - {n}))"
        by (rule Max_Im_ge)
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

