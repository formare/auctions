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

header {* Soundness verification of the second price single good auction *}

theory FullySpecifiedSecondPriceAuctionSoundness
imports
  FullySpecifiedSecondPriceAuction
  SingleGoodAuctionProperties

begin

lemma rel_all_fs_spa_is_spa:
  fixes A :: single_good_auction
    and B :: single_good_auction
    and t :: tie_breaker
  assumes A_fs_spa: "rel_all_sga_pred (fs_spa_pred' t) A"
      and B_spa: "rel_all_sga_pred spa_pred B"
  shows "A \<subseteq> B"
using assms fs_spa_is_spa sga_pred_imp_lift_to_rel_all
by (metis fs_spa_pred'_def)

(* TODO CL: simplify this now that we have rel_all (at least for combinatorial auctions; need to port it here) *)
lemma fs_spa_is_left_total :
  fixes A :: single_good_auction
    and t :: tie_breaker
  assumes wb_tie: "\<forall>N . wb_tie_breaker_on t N"
      and fs_spa: "rel_all_sga_pred (fs_spa_pred' t) A"
  shows "sga_left_total A spa_admissible_input"
proof (rule sga_left_totalI)
  fix N :: "participant set" and b :: bids
  assume admissible: "spa_admissible_input N b"
  (* Note that Isabelle says that "Max {}" exists (but of course can't specify it).
     However we are working with our own wrapped maximum definition anyway. *)
  with wb_tie obtain winner::participant where winner_def: "winner \<in> N \<and> winner = the (arg_max_tb_req_wb N t b)"
    using spa_admissible_input_def arg_max_def maximum_defined_def arg_max_tb_imp_arg_max
    by (smt mem_Collect_eq) 
    (* CL: alternative proof, not obvious either:
       by (metis fs_spa_pred_allocation_payments fs_spa_pred_def vectors_equal_def)
       But for didactic purposes we prefer the former, as it uses knowledge that can be assumed to be known already,
       whereas fs_spa_pred_allocation_payments logically comes after case-checking. *)
  (* Now that we know the winner exists, let's construct a suitable allocation and payments. *)
  def x \<equiv> "\<lambda> i::participant . if i = winner then 1::real else 0"
  def p \<equiv> "\<lambda> i::participant . if i = winner then maximum (N - {i}) b else 0"
  from x_def p_def winner_def wb_tie admissible
    have "fs_spa_pred N b t x p"
    unfolding
      second_price_auction_winner_outcome_def second_price_auction_loser_outcome_def fs_spa_pred_def
    by force
  with fs_spa show "\<exists> (x :: allocation) (p :: payments) . ((N, b), (x, p)) \<in> A"
    unfolding fs_spa_pred'_def rel_all_sga_pred_def by fast
qed

lemma fs_spa_winner_from_rel:
  assumes "rel_all_sga_pred (fs_spa_pred' t) A"
      and "((N, b), (x, p)) \<in> A"
  obtains winner where "winner \<in> N \<and> winner = the (arg_max_tb_req_wb N t b)"
      and "x winner = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0)"
      and "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
proof -
  from assms obtain winner::participant
    where "winner \<in> N \<and> winner = the (arg_max_tb_req_wb N t b)"
      and "x winner = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0)"
      and "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
    unfolding rel_all_sga_pred_def fs_spa_pred'_def
      fs_spa_pred_def second_price_auction_winner_outcome_def second_price_auction_loser_outcome_def
    by blast
  then show ?thesis ..
qed

(* TODO CL: simplify this now that we have rel_all (at least for combinatorial auctions; need to port it here) *)
lemma fs_spa_is_right_unique :
  fixes A :: single_good_auction
    and t :: tie_breaker
  assumes fs_spa: "rel_all_sga_pred (fs_spa_pred' t) A"
  shows "fs_sga_right_unique A spa_admissible_input"
unfolding fs_sga_right_unique_def
proof (rule sga_right_uniqueI)
  fix N :: "participant set" and b :: bids
  assume admissible: "spa_admissible_input N b"
  fix x :: allocation and x' :: allocation and p :: payments and p' :: payments

  assume "((N, b), (x, p)) \<in> A"
  with fs_spa obtain winner::participant
    where range: "winner \<in> N \<and> winner = the (arg_max_tb_req_wb N t b)"
      and alloc: "x winner = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0)"
      and pay: "p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)"
    by (rule fs_spa_winner_from_rel)
  
  assume "((N, b), (x', p')) \<in> A"
  with fs_spa obtain winner'::participant
    where range': "winner' \<in> N \<and> winner' = the (arg_max_tb_req_wb N t b)"
      and alloc': "x' winner' = 1 \<and> (\<forall> j \<in> N . j \<noteq> winner' \<longrightarrow> x' j = 0)"
      and pay': "p' winner' = maximum (N - {winner'}) b \<and> (\<forall>j \<in> N . j \<noteq> winner' \<longrightarrow> p' j = 0)"
    by (rule fs_spa_winner_from_rel)

  from range alloc pay range' alloc' pay' show "eq N x x' \<and> eq N p p'" unfolding eq_def by metis
qed

(* TODO CL: So far this just shows that the allocation is well-defined.  We should also prove that
   the payments are, say, non-negative. *)
(* TODO CL: port CombinatorialAuctionProperties.wd_outcomeI and use it here. *)
lemma fs_spa_well_defined_outcome :
  fixes A :: single_good_auction
    and t :: tie_breaker
  assumes "rel_all_sga_pred (fs_spa_pred' t) A"
  shows "sga_well_defined_outcome A sga_outcome_allocates"
  using assms
  unfolding rel_all_sga_pred_def fs_spa_pred'_def
  using fs_spa_is_spa spa_allocates
    sga_outcome_allocates_def sga_well_defined_outcome_def
  by (smt prod_caseI2 prod_caseI2')

theorem fs_spa_case_check :
  fixes A :: single_good_auction
    and t :: tie_breaker
  assumes wb_tie: "\<forall>N . wb_tie_breaker_on t N"
      and fs_spa: "rel_all_sga_pred (fs_spa_pred' t) A"
  shows "fs_sga_case_check A spa_admissible_input sga_outcome_allocates"
proof -
  from wb_tie fs_spa have "sga_left_total A spa_admissible_input" by (rule fs_spa_is_left_total)
  moreover from fs_spa have "fs_sga_right_unique A spa_admissible_input" by (rule fs_spa_is_right_unique)
  moreover from fs_spa have "sga_well_defined_outcome A sga_outcome_allocates"
    by (rule fs_spa_well_defined_outcome)
  ultimately show ?thesis unfolding fs_sga_case_check_def by simp
qed

end
