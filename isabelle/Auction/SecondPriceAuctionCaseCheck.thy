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

header {* Case check of Second price single good auctions *}

theory SecondPriceAuctionCaseCheck
imports FullySpecifiedSecondPriceAuctionCaseCheck 
begin

(* TODO CL: This lemma also works when admissibility is defined as "card N > 0" because
   when we compute the second-highest bid for the payments vector, card N = 0 will 
   boil down to the question of whether Max {} exists.  Isabelle says that it exists; to see this try

lemma max_exists : "\<exists>x . x = Max {}" by blast

  This is an inherent trait of Isabelle's HOL implementation: all functions are total in principle, 
  just sometimes underspecified, so that you don't know _what_ "Max {}" is.  To see this try

value "Max {}"

  vs.

value "Max {1::nat, 2}"

  Isabelle supports partial functions.  One can either use explicit undefinedness (using the Option datatype with the None and Some constructors),
  but that would affect and thus bloat large parts of our formalisation.

  In "isabelle doc functions" section 7 there is also something that looks like a more sophisticated support for 
  partial functions.

  For now, spa_is_left_total doesn't catch the case "card N = 1", but spa_vickrey_payment, which is
  part of our checks whether the outcome is well-defined, doesn't work for "case N = 1".  For precise
  details, see the comment in spa_vickrey_payment.

  So, @CR, this is really a good justification for why we need spa_vickrey_payment.  Indeed the whole
  battery of case checks now covers: "for each admissible input there is (that's left-totality) a 
  unique (that's right-uniqueness), well-defined (that's spa_vickrey_payment and spa_allocates) outcome."
*)
text{* Our relational definition of second price auction is left-total. *}
lemma spa_is_left_total :
  fixes A :: single_good_auction
  (* A is the set of all second price auctions.
     Assuming "second_price_auction A" would merely mean that all elements of A are second price auctions,
     which is not enough here. *)
  assumes spa: "rel_all_sga_pred spa_pred A"
  shows "sga_left_total A spa_admissible_input"
proof -
  (* We define ourselves an arbitrary tie breaker *)
  have foo: "\<exists>t . \<forall>N . wb_tie_breaker_on t N"
  (* TODO CL: If the following ever gets deleted _here_, preserve it somewhere else in the toolbox. *)
  proof -
    def t \<equiv> "op>::(participant \<Rightarrow> participant \<Rightarrow> bool)"
    then have wb_tie: "\<forall>N . wb_tie_breaker_on t N" unfolding wb_tie_breaker_on_def
      strict_linear_order_on_def trans_def irrefl_def total_on_def 
      by (smt bot_least insert_subset mem_Collect_eq prod.cases)
    then show ?thesis by blast
  qed
  then obtain t where wb_tie: "\<forall>N . wb_tie_breaker_on t N" by (smt someI_ex)
  (* Note that it is not necessary to prove that fs_spa_pred' is satisfiable. *)
  def fs_spa_pred'' \<equiv> "\<lambda> tup . (\<exists> N b x p . tup = ((N, b), (x, p)) \<and> (fs_spa_pred' t) N b x p)"
  then have "\<exists> A . (\<forall> tup . tup \<in> A \<longleftrightarrow> fs_spa_pred'' tup)" by (metis mem_Collect_eq)
  with fs_spa_pred''_def have "\<exists> A . (\<forall> a b c d . ((a, b), (c, d)) \<in> A \<longleftrightarrow> (fs_spa_pred' t) a b c d)" by simp
  then obtain B where B_fs_spa: "rel_all_sga_pred (fs_spa_pred' t) B" unfolding rel_all_sga_pred_def ..
  with spa have sup: "B \<subseteq> A" using rel_all_fs_spa_is_spa by simp
  from B_fs_spa wb_tie fs_spa_is_left_total have B_left_total: "sga_left_total B spa_admissible_input" by simp
  then show ?thesis using sup by (rule left_total_suprel)
qed
(* alternative direct proof:
proof (rule sga_left_totalI)
  fix N :: "participant set" and b :: bids
  assume admissible: "spa_admissible_input N b"
  from admissible obtain winner::participant where winner_def: "winner \<in> N \<and> winner \<in> arg_max N b"
    using spa_admissible_input_def arg_max_def maximum_defined_def maximum_is_component
    by (smt mem_Collect_eq)
  def x \<equiv> "\<lambda> i::participant . if i = winner then 1::real else 0"
  def p \<equiv> "\<lambda> i::participant . if i = winner then maximum (N - {i}) b else 0"
  from x_def p_def winner_def admissible
    have "spa_pred N b x p"
    unfolding
      second_price_auction_winner_outcome_def second_price_auction_loser_outcome_def spa_pred_def
    by force
  with spa show "\<exists> (x :: allocation) (p :: payments) . ((N, b), (x, p)) \<in> A"
    unfolding rel_all_sga_pred_def by fast
qed
*)

text{* We consider two outcomes of a second price auction equivalent if 
\begin{enumerate}
\item the bids of the participants to which the good is allocated are equal
\item the bids of the participants with positive payments are equal
\end{enumerate}
This should be as weak as possible, as not to accidentally restate the full definition of a second price auction.
 *}
definition spa_equivalent_outcome :: "participant set \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where "spa_equivalent_outcome N b x p x' p' \<longleftrightarrow> 
    b ` { i \<in> N . x i = 1 } = b ` { i \<in> N . x' i = 1 } \<and>
    b ` { i \<in> N . p i > 0 } = b ` { i \<in> N . p' i > 0 }"
(* This definition is more general in that it allow for divisible goods. *)

text{* Under certain conditions we can show that 
  the bids of the participant set with positive payments are equal
  (one direction of the equality) *}
lemma positive_payment_bids_eq_suff :
  fixes N :: "participant set"
    and winner :: participant
    and b :: bids
    and p :: payments
    and p' :: payments
  assumes admissible: "spa_admissible_input N b"
      and range: "winner \<in> N \<and> winner \<in> arg_max N b"
      and pay: "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
      and range': "winner' \<in> N \<and> winner' \<in> arg_max N b"
      and pay': "p' winner' = maximum (N - {winner'}) b \<and> (\<forall>j \<in> N . j \<noteq> winner' \<longrightarrow> p' j = 0)"
  shows "b ` { i \<in> N . p i > 0 } \<subseteq> b ` { i \<in> N . p' i > 0 }"
proof (intro subsetI)
  from admissible have bids: "bids N b" and ge2: "card N > 1"
    using spa_admissible_input_def by auto
  fix bid assume premise: "bid \<in> b ` { i \<in> N . p i > 0 }"
  with range pay range' have bw': "bid = b winner'" unfolding arg_max_def by force
  from premise pay have p_positive: "p winner > 0" by auto
  with ge2 range pay have bwpos: "b winner > 0"
    using arg_max_def maximum_except_defined maximum_remaining_maximum by (smt mem_Collect_eq)
  from ge2 range' have md: "maximum_defined (N - {winner'})" using maximum_except_defined by (auto simp only: conjE)
  have "maximum (N - {winner'}) b > 0"
  proof (rule ccontr)
    assume assm: "\<not> maximum (N - {winner'}) b > 0"
    {
      fix i assume i_range: "i \<in> (N - {winner'})"
      with bids have bipos: "b i \<ge> 0" unfolding bids_def non_negative_def le_def zero_def by blast
      from md have "maximum (N - {winner'}) b \<ge> b i" using i_range by (rule maximum_is_greater_or_equal)
      then have "maximum (N - {winner'}) b = 0" using assm bipos by simp
    }
    with assm range range' pay pay' have foow': "maximum (N - {winner'}) b = 0"
      using maximum_is_component md by metis
    show False
    proof cases
      assume "winner' = winner"
      then show False using p_positive pay foow' by auto
    next
      assume "winner' \<noteq> winner"
      with range have "winner \<in> N - {winner'}" by fast
      then have x: "maximum (N - {winner'}) b \<ge> b winner" using range md by (simp only: maximum_is_greater_or_equal)
      with foow' have bwzn: "b winner \<le> 0" by auto
      from range have "maximum N b = b winner" unfolding arg_max_def by auto
      with md x maximum_remaining_maximum bwpos bwzn show False by auto
    qed
  qed
  then show "bid \<in> b ` { i \<in> N . p' i > 0 }" using range' pay' bw' by auto
qed

lemma spa_winner_from_rel:
  assumes "rel_all_sga_pred spa_pred A"
      and "((N, b), (x, p)) \<in> A"
  obtains winner where "winner \<in> N \<and> winner \<in> arg_max N b"
      and "x winner = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0)"
      and "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
proof -
  from assms obtain winner::participant
    where "winner \<in> N \<and> winner \<in> arg_max N b"
      and "x winner = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0)"
      and "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
    unfolding rel_all_sga_pred_def 
      spa_pred_def second_price_auction_winner_outcome_def second_price_auction_loser_outcome_def
    by smt (* Interestingly the corresponding step in fs_spa_winner_from_rel works by blast. *)
  then show ?thesis ..
qed

text{* Our relational definition of second price auction is right-unique. *}
lemma spa_is_right_unique :
  fixes A :: single_good_auction
  (* A is the set of all second price auctions.
     Assuming "second_price_auction A" would merely mean that all elements of A are second price auctions,
     which is not enough here. *)
  assumes spa: "rel_all_sga_pred spa_pred A"
  shows "sga_right_unique A spa_admissible_input spa_equivalent_outcome"
proof (rule sga_right_uniqueI)
  fix N :: "participant set" and b :: bids
  assume admissible: "spa_admissible_input N b"
  fix x :: allocation and x' :: allocation and p :: payments and p' :: payments

  assume "((N, b), (x, p)) \<in> A"
  with spa obtain winner::participant
    where range: "winner \<in> N \<and> winner \<in> arg_max N b"
      and alloc: "x winner = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0)"
      and pay: "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
    by (rule spa_winner_from_rel)

  assume "((N, b), (x', p')) \<in> A"
  with spa obtain winner'::participant
    where range': "winner' \<in> N \<and> winner' \<in> arg_max N b"
      and alloc': "x' winner' = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner' \<longrightarrow> x' j = 0)"
      and pay': "p' winner' = maximum (N - {winner'}) b \<and> (\<forall>j \<in> N . j \<noteq> winner' \<longrightarrow> p' j = 0)"
    by (rule spa_winner_from_rel)

  have "b ` { i \<in> N . x i = 1 } = b ` { i \<in> N . x' i = 1 }" (is "?lhs = ?rhs")
  proof (* CL: any way to collapse these two cases into one?  Preferably in Isar style? *)
    from range alloc range' alloc' show "?lhs \<subseteq> ?rhs"
      unfolding arg_max_def by auto
  next
    from range' alloc' range alloc show "?rhs \<subseteq> ?lhs"
      unfolding arg_max_def by auto
  qed
  moreover have "b ` { i \<in> N . p i > 0 } = b ` { i \<in> N . p' i > 0 }" (is "?lhs = ?rhs")
  proof (* CL: any way to collapse these two cases into one?  Preferably in Isar style? *)
    from admissible range pay range' pay' show "?lhs \<subseteq> ?rhs"
      by (rule positive_payment_bids_eq_suff)
  next
    from admissible range' pay' range pay show "?rhs \<subseteq> ?lhs"
      by (rule positive_payment_bids_eq_suff)
  qed
  ultimately show "spa_equivalent_outcome N b x p x' p'" unfolding spa_equivalent_outcome_def ..
qed

(* TODO CL: merge with fs_spa_well_defined_outcome *)
lemma spa_well_defined_outcome :
  fixes A :: single_good_auction
  assumes "rel_all_sga_pred spa_pred A"
  shows "sga_well_defined_outcome A sga_outcome_allocates"
  using assms
  unfolding rel_all_sga_pred_def fs_spa_pred'_def
  using spa_allocates sga_outcome_allocates_def sga_well_defined_outcome_def
  by (smt prod_caseI2 prod_caseI2')

theorem spa_case_check :
  fixes A :: single_good_auction
  assumes spa: "rel_all_sga_pred spa_pred A"
  shows "sga_case_check A spa_admissible_input spa_equivalent_outcome sga_outcome_allocates"
proof -
  from spa have "sga_left_total A spa_admissible_input" by (rule spa_is_left_total)
  moreover from spa have "sga_right_unique A spa_admissible_input spa_equivalent_outcome" by (rule spa_is_right_unique)
  moreover from spa have "sga_well_defined_outcome A sga_outcome_allocates" by (rule spa_well_defined_outcome)
  ultimately show ?thesis unfolding sga_case_check_def by simp
qed

end
