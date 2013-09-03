(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <m.kerber@cs.bham.ac.uk>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Makarius Wenzel <wenzel@lri.fr>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Second price single good auctions and some of their properties *}

theory FullySpecifiedSecondPriceAuction
imports SingleGoodAuction SingleGoodAuctionTieBreaker SecondPriceAuction UniqueMaximum
   "~~/src/HOL/Library/Efficient_Nat"
begin

(* fs = fully specified *)
definition fs_spa_pred :: "participant set \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "fs_spa_pred N b t x p \<longleftrightarrow>
      wb_tie_breaker_on t N \<and>
      spa_admissible_input N b \<and>
      (\<exists>i \<in> N . i = the (arg_max_tb_req_wb N t b) \<and> second_price_auction_winner_outcome N b x p i \<and>
        (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> second_price_auction_loser_outcome N x p j))"

text{* convenience function to compute the winner of a fully specified second price auction with tie-breaking *}
fun fs_spa_winner_req_wb :: "participant set \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> participant"
  where "fs_spa_winner_req_wb N b t = the (arg_max_tb_req_wb N t b)"

fun fs_spa_winner :: "participant set \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> participant"
  where "fs_spa_winner N b t = arg_max_tb N t b"

lemma fs_spa_winner_wb:
  assumes "wb_tie_breaker_on t N" shows "fs_spa_winner N b t = fs_spa_winner_req_wb N b t"
  using assms by simp

text{* convenience function to compute the allocation of a fully specified second price auction with tie-breaking *}
fun fs_spa_allocation_req_wb :: "participant set \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> allocation"
  where "fs_spa_allocation_req_wb N b t = (let winner = fs_spa_winner_req_wb N b t in
    (\<lambda> i . if (i = winner) then 1 else 0))"

fun fs_spa_allocation :: "participant set \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> allocation"
  where "fs_spa_allocation N b t = (let winner = fs_spa_winner N b t in
    (\<lambda> i . if (i = winner) then 1 else 0))"

lemma fs_spa_allocation_wb:
  assumes "wb_tie_breaker_on t N" shows "fs_spa_allocation N b t = fs_spa_allocation_req_wb N b t"
  using assms by simp

text{* convenience function to compute the payments of a fully specified second price auction with tie-breaking *}
fun fs_spa_payments_req_wb :: "participant set \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> payments"
  where "fs_spa_payments_req_wb N b t = (let winner = fs_spa_winner_req_wb N b t in
    (\<lambda> i . if (i = winner) then maximum (N - {i}) b else 0))"

fun fs_spa_payments :: "participant set \<Rightarrow> bids \<Rightarrow> tie_breaker \<Rightarrow> payments"
  where "fs_spa_payments N b t = (let winner = fs_spa_winner N b t in
    (\<lambda> i . if (i = winner) then maximum (N - {i}) b else 0))"

lemma fs_spa_payments_wb:
  assumes "wb_tie_breaker_on t N" shows "fs_spa_payments N b t = fs_spa_payments_req_wb N b t"
  using assms by simp

text{* The definitions of the computable functions @{text fs_spa_allocation} and @{text fs_spa_payments}
  are consistent with how we defined the outcome of a fully specified second price auction
  with tie-breaking in @{text fs_spa_pred}. *}
lemma fs_spa_pred_allocation_payments:
  fixes N :: "participant set"
    and b :: bids
    and t :: tie_breaker
    and x :: allocation
    and p :: payments
  shows "fs_spa_pred N b t x p \<longleftrightarrow>
    wb_tie_breaker_on t N \<and>
    spa_admissible_input N b \<and>
    eq N x (fs_spa_allocation_req_wb N b t) \<and>
    eq N p (fs_spa_payments_req_wb N b t)" (is "?fs_spa_pred \<longleftrightarrow> ?alloc_pay")
proof
  assume "?fs_spa_pred"
  then have "wb_tie_breaker_on t N \<and> spa_admissible_input N b"
    and outcome: "\<exists>i \<in> N . i = fs_spa_winner_req_wb N b t \<and>
     x i = 1 \<and> (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> x j = 0) \<and>
     p i = maximum (N - {i}) b \<and> (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> p j = 0)"
    unfolding fs_spa_pred_def
      second_price_auction_winner_outcome_def second_price_auction_loser_outcome_def
    by auto
  then show "?alloc_pay"
    using fs_spa_allocation_req_wb.simps fs_spa_payments_req_wb.simps unfolding eq_def by smt
next
  assume "?alloc_pay"
  then have wb_tie: "wb_tie_breaker_on t N"
    and admissible: "spa_admissible_input N b"
    and outcome: "let winner = fs_spa_winner_req_wb N b t in
      (\<forall>i \<in> N . x i = (if (i = winner) then 1 else 0)) \<and>
      (\<forall>i \<in> N . p i = (if (i = winner) then maximum (N - {i}) b else 0))"
    unfolding eq_def
    by simp_all
  from wb_tie admissible have winner_range: "fs_spa_winner_req_wb N b t \<in> N"
    using arg_max_def arg_max_tb_imp_arg_max fs_spa_winner_req_wb.simps maximum_defined_def spa_admissible_input_def
      mem_Collect_eq
    by smt
  with outcome have "let winner = fs_spa_winner_req_wb N b t in
      x winner = 1 \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> x j = 0) \<and>
      p winner = maximum (N - {winner}) b \<and> (\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> p j = 0)" by metis
  with wb_tie admissible winner_range show "?fs_spa_pred"
     unfolding fs_spa_pred_def
       second_price_auction_winner_outcome_def second_price_auction_loser_outcome_def
     using fs_spa_winner_req_wb.simps by metis
qed

lemma fs_spa_is_spa :
  fixes N :: "participant set"
    and b :: bids
    and t :: tie_breaker
    and x :: allocation
    and p :: payments
  assumes "fs_spa_pred N b t x p"
  shows "spa_pred N b x p"
proof -
  from assms have wb_tie: "wb_tie_breaker_on t N" and card: "card N > 1" and bids: "bids N b" and
    def_unfolded: "(\<exists>i \<in> N . i = the (arg_max_tb_req_wb N t b) \<and> second_price_auction_winner_outcome N b x p i \<and>
      (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> second_price_auction_loser_outcome N x p j))"
    unfolding fs_spa_pred_def spa_admissible_input_def by auto
  then obtain winner
    where fs_spa_winner: "winner \<in> N \<and> winner = the (arg_max_tb_req_wb N t b) \<and>
        second_price_auction_winner_outcome N b x p winner"
      and spa_loser: "\<forall>j \<in> N . j \<noteq> winner \<longrightarrow> second_price_auction_loser_outcome N x p j" by blast
  have spa_winner: "winner \<in> N \<and> winner \<in> arg_max N b \<and> second_price_auction_winner_outcome N b x p winner"
  proof -
    from fs_spa_winner have range: "winner \<in> N"
      and determination: "winner = the (arg_max_tb_req_wb N t b)"
      and spa_winner_outcome: "second_price_auction_winner_outcome N b x p winner"
      by auto
    from card have maximum_defined: "maximum_defined N" unfolding maximum_defined_def by simp
    with wb_tie determination have "winner \<in> arg_max N b" using arg_max_tb_imp_arg_max by simp
    with range and spa_winner_outcome show ?thesis by simp
  qed
  with card bids spa_loser have "card N > 1 \<and> bids N b \<and> (\<exists>i \<in> N. i \<in> arg_max N b \<and> second_price_auction_winner_outcome N b x p i \<and>
    (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> second_price_auction_loser_outcome N x p j))" by blast
  then show ?thesis unfolding spa_admissible_input_def spa_pred_def by simp
qed

text{* alternative definition for easier currying *}
definition fs_spa_pred' :: "tie_breaker \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where "fs_spa_pred' t N b x p = fs_spa_pred N b t x p"

code_include Scala ""
{*package code
*}
export_code fs_spa_winner fs_spa_allocation fs_spa_payments in Scala
(* In SML, OCaml and Scala "file" is a file name; in Haskell it's a directory name ending with / *)
module_name Vickrey file "code/generated/code.scala"
(* A trivial example to try interactively with the generated Scala code:

:load code.scala
Vickrey.times_int(Vickrey.Zero_int(), Vickrey.Zero_int())

Notes:
* There are apparently no ready-to-use code-unfold theorems (codegen \<section>2.2) in the library.
*)
(*
print_codeproc
*)

end
