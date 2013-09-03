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

theory SecondPriceAuction
imports SingleGoodAuction Maximum
begin

text{* Agent @{text i} being the winner of a second-price auction (see below for complete definition) means
\begin{itemize}
\item he/she is one of the participants with the highest bids
\item he/she wins the auction
\item and pays the maximum price that remains after removing the winner's own bid from the vector of bids.
\end{itemize} *}
definition second_price_auction_winner_outcome ::
    "participant set \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where
    "second_price_auction_winner_outcome N b x p i \<longleftrightarrow>
      x i = 1 \<and> p i = maximum (N - {i}) b"

definition second_price_auction_winner ::
    "participant set \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where
    "second_price_auction_winner N b x p i \<longleftrightarrow>
      i \<in> N \<and> i \<in> arg_max N b \<and>
      second_price_auction_winner_outcome N b x p i"

text{* Agent @{text i} being a loser of a second-price auction (see below for complete definition) means
\begin{itemize}
\item he/she loses the auction
\item and pays nothing
\end{itemize} *}
definition second_price_auction_loser_outcome ::
    "participant set \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where "second_price_auction_loser_outcome N x p i \<longleftrightarrow>
     x i = 0 \<and>
     p i = 0"

definition second_price_auction_loser ::
    "participant set \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where "second_price_auction_loser N x p i \<longleftrightarrow> i \<in> N \<and>
     second_price_auction_loser_outcome N x p i"

definition spa_admissible_input :: "participant set \<Rightarrow> bids \<Rightarrow> bool"
  where "spa_admissible_input N b \<longleftrightarrow> card N > 1 \<and> bids N b"

text{* A second-price auction is an auction whose outcome satisfies the following conditions:
\begin{enumerate}
\item One of the participants with the highest bids wins. (We do not formalise the random selection of one distinct participants from the set of highest bidders,
in case there is more than one.)
\item The price that the winner pays is the maximum bid that remains after removing the winner's own bid from the vector of bids.
\item The losers do not pay anything.
\end{enumerate} *}
definition spa_pred :: "participant set \<Rightarrow> bids \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "spa_pred N b x p \<longleftrightarrow>
      spa_admissible_input N b \<and>
      (\<exists>i \<in> N. i \<in> arg_max N b \<and> second_price_auction_winner_outcome N b x p i \<and>
        (\<forall>j \<in> N . j \<noteq> i \<longrightarrow> second_price_auction_loser_outcome N x p j))"

definition second_price_auction :: "single_good_auction \<Rightarrow> bool"
  where "second_price_auction = rel_sat_sga_pred spa_pred"

text{* definition of a second price auction, projected to the allocation *}
lemma spa_allocation :
  fixes N :: "participant set" and b :: bids
    and x :: allocation and p :: payments
  assumes "spa_pred N b x p"
  shows "\<exists> i \<in> N . x i = 1 \<and> (\<forall> j \<in> N . j \<noteq> i \<longrightarrow> x j = 0)"
  using assms
  unfolding spa_pred_def second_price_auction_def
    second_price_auction_winner_outcome_def
    second_price_auction_loser_outcome_def
  by auto

lemma sga_pred_imp_lift_to_rel_all:
  fixes p q A B
  assumes PA: "rel_all_sga_pred p A"
      and QB: "rel_all_sga_pred q B"
      and p_imp_q: "\<And> N b x p' . ((N, b), (x, p')) \<in> A \<Longrightarrow> p N b x p' \<Longrightarrow> q N b x p'"
    shows "A \<subseteq> B" using PA QB p_imp_q unfolding rel_all_sga_pred_def by force

text{* Our second price auction (@{text spa_pred}) is well-defined in that its outcome is an allocation. *}
lemma spa_allocates :
  fixes N :: "participant set" and b :: bids
    and x :: allocation and p :: payments
  assumes spa: "spa_pred N b x p"
  shows "allocation N x"
proof -
  from spa have "card N > 0" unfolding spa_pred_def spa_admissible_input_def by simp
  from spa obtain i where i_def: "i \<in> N \<and> x i = 1" using spa_allocation by blast
  (* the losers' allocations are all 0 *)
  with spa have j_def: "\<forall>j \<in> N - {i} . x j = 0" using spa_allocation by (metis member_remove remove_def)
  then have "(\<Sum> k \<in> N . x k) = 1"
    using `card N > 0` i_def
    by (metis (mono_tags) card_ge_0_finite monoid_add_class.add.right_neutral setsum.neutral setsum.remove setsum_infinite)
  then show ?thesis unfolding allocation_def non_negative_def le_def zero_def by (smt spa spa_allocation)
qed

text{* definition of a second price auction, projected to the payments *}
lemma spa_payments :
  fixes N :: "participant set" and b :: bids
    and x :: allocation and p :: payments
  assumes "spa_pred N b x p"
  shows "\<exists> i \<in> N . p i = maximum (N - {i}) b \<and> (\<forall> j \<in> N . j \<noteq> i \<longrightarrow> p j = 0)"
  using assms
  unfolding spa_pred_def second_price_auction_winner_outcome_def second_price_auction_loser_outcome_def
  by blast
(* TODO CL: In the general auction case it may make sense to check that the payments (including the seller's payment)
   sum up to 0.
*)
text{* Our second price auction (@{text spa_pred}) is well-defined in that its outcome specifies non-negative payments for everyone. *}
lemma spa_vickrey_payment :
  fixes N :: "participant set" and b :: bids
    and x :: allocation and p :: payments
  assumes spa: "spa_pred N b x p"
  shows "vickrey_payment N p"
proof -
  from spa have card_N: "card N > 1" unfolding spa_pred_def spa_admissible_input_def by simp
  then have maximum_defined: "maximum_defined N" unfolding spa_pred_def maximum_defined_def by auto
  from spa obtain i where i_range: "i \<in> N"
    and i_pay: "p i = maximum (N - {i}) b"
    and losers_pay: "\<forall> j \<in> N . j \<noteq> i \<longrightarrow> p j = 0"
    using spa_payments by blast
  (* Note that if "card N = 1" were allowed, there would be no such k.  This seems fine for now,
     but in the next step it becomes apparent what we need "card N = 1" and thus this k_def for:
     for obtaining the fact `greater`, which talks about the second-highest bid and assumes 
     that it is defined. *)
  from card_N and i_range obtain k where k_def: "k \<in> N \<and> k \<noteq> i"
    using  maximum_except_defined maximum_is_component
    by (metis Diff_iff insertCI)
  from k_def and maximum_defined have greater: "maximum (N - {i}) b \<ge> b k" using maximum_except_is_greater_or_equal by blast
  also have "\<dots> \<ge> 0" using spa spa_pred_def second_price_auction_def spa_admissible_input_def bids_def non_negative_def le_def zero_def by (smt greater k_def)
  with i_pay and calculation have "p i \<ge> 0" by simp
  with i_range and losers_pay have "\<forall> k \<in> N . p k \<ge> 0" by auto
  with vickrey_payment_def show ?thesis ..
qed

lemma spa_is_sga_pred :
  fixes N :: "participant set" and b :: bids
    and x :: allocation and p :: payments
  assumes "spa_pred N b x p"
  shows "sga_pred N b x p"
  using assms
  unfolding spa_pred_def spa_admissible_input_def sga_pred_def by simp

lemma sga_pred_imp_lift_to_rel_sat:
  fixes P Q p q A
  assumes P_def: "P = rel_sat_sga_pred p"
      and Q_def: "Q = rel_sat_sga_pred q"
      and PA: "P A"
      and p_imp_q: "\<And> N b x p' . ((N, b), (x, p')) \<in> A \<Longrightarrow> p N b x p' \<Longrightarrow> q N b x p'"
  shows "Q A" using PA p_imp_q unfolding P_def Q_def rel_sat_sga_pred_def by blast

lemma spa_is_sga :
  fixes A :: single_good_auction
  assumes spa: "second_price_auction A"
  shows "single_good_auction A"
using second_price_auction_def single_good_auction_def spa spa_is_sga_pred
by (rule sga_pred_imp_lift_to_rel_sat)

lemma spa_allocates_binary :
  fixes N :: "participant set" and b :: bids
    and x :: allocation and p :: payments
    and i :: participant
  assumes "spa_pred N b x p"
      and "i \<in> N"
  shows "x i = 0 \<or> x i = 1"
  using assms
  unfolding spa_pred_def second_price_auction_def second_price_auction_winner_outcome_def second_price_auction_loser_outcome_def
  by fast

(*
text{* We chose not to \emph{define} that a second-price auction has only one winner, as it is not necessary.  Therefore we have to prove it. *}
(* TODO CL: discuss whether it makes sense to keep this lemma -- it's not used for "theorem vickreyA" but might still be useful for the toolbox *)
lemma second_price_auction_has_only_one_winner:
  fixes n::participants and x::allocation and p::payments and b::"real vector"
    and winner::participant and j::participant
  assumes "second_price_auction n x p"
    and "bids n b"
    and "second_price_auction_winner n b x p winner"
    and "second_price_auction_winner n b x p j"
  shows "j = winner"
  using assms
  unfolding second_price_auction_def second_price_auction_winner_def
  using allocation_unique
  by blast
*)

text{* The participant who gets the good also satisfies the further properties of a second-price auction winner. *}
lemma allocated_implies_spa_winner:
  fixes N :: "participant set" and b :: bids
     and x :: allocation and p :: payments
     and winner :: participant
  assumes "spa_pred N b x p"
    and "winner \<in> N"
    and "x winner = 1"
  shows "second_price_auction_winner N b x p winner"
  using assms
  unfolding spa_pred_def second_price_auction_def second_price_auction_winner_def second_price_auction_loser_outcome_def
    allocation_def
  by (metis zero_neq_one)
    (* CL: With the generalised allocation_def, this proof needed a bit more complexity,
         as "x winner = 1" implies "x i = 0" for all other participants is rather implicit now. *)

text{* A participant who doesn't gets the good satisfies the further properties of a second-price auction loser. *}
lemma not_allocated_implies_spa_loser:
  fixes N :: "participant set" and b :: bids
    and x :: allocation and p :: payments
    and loser :: participant
  assumes spa: "spa_pred N b x p"
    and range: "loser \<in> N"
    and loses: "x loser = 0"
  shows "second_price_auction_loser N x p loser"
proof -
  from loses have "\<not> second_price_auction_winner N b x p loser"
    unfolding second_price_auction_winner_def second_price_auction_winner_outcome_def by simp
  with spa range show ?thesis
    unfolding spa_pred_def second_price_auction_winner_def second_price_auction_loser_def
    by fast
qed

text{* If there is only one bidder with a maximum bid, that bidder wins. *}
lemma only_max_bidder_wins:
  fixes N :: "participant set" and max_bidder :: participant
    and b :: bids and x :: allocation and p :: payments
  assumes defined: "maximum_defined N"
    and spa: "spa_pred N b x p"
    and range: "max_bidder \<in> N"
    and only_max_bidder: "b max_bidder > maximum (N - {max_bidder}) b"
  shows "second_price_auction_winner N b x p max_bidder"
proof -
  from spa have spa_unfolded:
    "spa_admissible_input N b \<and> (\<exists>i. i \<in> arg_max N b \<and> second_price_auction_winner_outcome N b x p i \<and>
      (\<forall>j \<in> N. j \<noteq> i \<longrightarrow> second_price_auction_loser_outcome N x p j))"
    unfolding spa_pred_def second_price_auction_def by blast
  {
    fix j :: participant
    assume j_not_max: "j \<in> N \<and> j \<noteq> max_bidder"
    have "j \<notin> arg_max N b"
    proof
      assume "j \<in> arg_max N b"
      then have maximum: "b j = maximum N b" unfolding arg_max_def by simp

      from defined j_not_max range have "b j \<le> maximum (N - {max_bidder}) b"
        using maximum_except_is_greater_or_equal by simp
      with only_max_bidder have *: "b j < b max_bidder" by simp

      from defined range maximum have "b j \<ge> b max_bidder"
        by (simp add: maximum_is_greater_or_equal)
      with * show False by simp
    qed
  }
  with spa_unfolded show ?thesis
    by (auto simp add: second_price_auction_winner_def arg_max_def)
qed

text{* a formula for computing the payoff of the winner of a second-price auction *}
lemma second_price_auction_winner_payoff:
  fixes N :: "participant set" and v :: valuations and x :: allocation
    and b :: bids and p :: payments and winner :: participant
  assumes defined: "maximum_defined N"
    and spa: "spa_pred N b x p"
    and i_range: "i \<in> N"
    and wins: "x i = 1"
  shows "payoff (v i) (x i) (p i) = v i - maximum (N - {i}) b"
proof -
  have "payoff (v i) (x i) (p i) = v i - p i"
    using wins unfolding payoff_def by simp
  also have "\<dots> = v i - maximum (N - {i}) b"
    using defined spa i_range wins
      using allocated_implies_spa_winner
    unfolding second_price_auction_winner_def second_price_auction_winner_outcome_def
    by simp
  finally show ?thesis .
qed

text{* a formula for computing the payoff of a loser of a second-price auction *}
lemma second_price_auction_loser_payoff:
  fixes N :: "participant set" and v :: valuations and x :: allocation
    and b :: bids and p :: payments and loser :: participant
  assumes "spa_pred N b x p"
    and "i \<in> N"
    and "x i = 0"
  shows "payoff (v i) (x i) (p i) = 0"
  using assms not_allocated_implies_spa_loser
  unfolding second_price_auction_loser_def second_price_auction_loser_outcome_def payoff_def
  by simp

text{* If a participant wins a second-price auction by not bidding his/her valuation,
  the payoff equals the valuation minus the remaining maximum bid. *}
lemma winners_payoff_on_deviation_from_valuation:
  fixes N :: "participant set" and v :: valuations and x :: allocation
    and b :: bids and p :: payments and winner :: participant
  assumes "spa_pred N b x p"
    and "i \<in> N"
    and "x i = 1"
    and "maximum_defined N"
  shows "payoff (v i) (x i) (p i) = v i - maximum (N - {i}) (b(i := v i))"
  using assms second_price_auction_winner_payoff remaining_maximum_invariant
  by simp

end
