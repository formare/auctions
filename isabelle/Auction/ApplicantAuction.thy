(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <m.kerber@cs.bham.ac.uk>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory ApplicantAuction
imports SecondPriceAuction
  (* TODO CL: refactor the former into even more little theories.
     Here, we import the whole SecondPriceAuction theory,
     but all we need is the definition of second_price_auction_winner *)

begin

(* TODO CL: The first version for this is a mere _copy_ of SecondPriceAuction, with things adapted as needed.
   We actually need to refactor this theory as well as SecondPriceAuction to reuse as much code as possible. *)

section{* Cramton's Applicant Auctions (simplified variant of simultaneous ascending clock auction) *}

text{* like a second-price auction, except that the money the winner pays is equally distributed among the losers *}
definition applicant_auction_loser :: "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> participant \<Rightarrow> bool"
  where "applicant_auction_loser n b x p winner i \<equiv> i \<in> {1..n} \<and> \<not>x b i 
                                                \<and> (p b i = -(second_price_auction_winners_payment n b winner) / (n - 1))"

definition applicant_auction :: "participants \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where "applicant_auction n x p \<equiv> n > 1 (* otherwise 'dividing the winner's payment among the losers' wouldn't make sense*)
    \<and> (\<forall>b::real_vector . bids n b \<longrightarrow> allocation n b x \<and> vickrey_payment n b p \<and>
      (\<exists>i::participant. i \<in> {1..n} \<and> second_price_auction_winner n b x p i (* unchanged *)
                        \<and> (\<forall>j::participant. j \<in> {1..n} \<and> j \<noteq> i \<longrightarrow> applicant_auction_loser n b x p i j)))"

lemma allocated_implies_aa_winner : (* unchanged from allocated_implies_spa_winner *)
  fixes n::participants and x::allocation and p::payments and b::real_vector and winner::participant
  assumes "applicant_auction n x p"
    and "bids n b"
    and "winner \<in> {1..n}"  (* in an earlier version we managed without this assumption, but it makes the proof easier *)
    and "x b winner"
  shows "second_price_auction_winner n b x p winner"
  using assms
  unfolding applicant_auction_def second_price_auction_winner_def
  using allocation_unique
  by blast

lemma not_allocated_implies_aa_loser :
  fixes n::participants and x::allocation and p::payments and b::real_vector and winner::participant and loser::participant
  assumes aa: "applicant_auction n x p"
    and bids: "bids n b"
    and winner: "second_price_auction_winner n b x p winner"
    and range: "loser \<in> {1..n}"
    and loses: "\<not> x b loser"
  shows "applicant_auction_loser n b x p winner loser"
proof - (* by contradiction *)
  {
    assume False: "\<not> applicant_auction_loser n b x p winner loser"
    have "x b loser"
      using aa bids unfolding applicant_auction_def 
      using False range winner allocation_unique
      using second_price_auction_winner_def
      by metis
    with loses have "False" ..
  }
  then show ?thesis by blast
qed

lemma applicant_auction_winner_payoff : (* unchanged from allocated_implies_spa_winner *)
  fixes n::participants and v::real_vector and x::allocation and b::real_vector and p::payments and winner::participant
  assumes aa: "applicant_auction n x p"
    and bids: "bids n b"
    and winner_range: "winner \<in> {1..n}"
    and wins: "x b winner"
  shows "payoff_vector v (x b) (p b) winner = v winner - maximum_except n b winner"
proof -
  have "payoff_vector v (x b) (p b) winner
    = payoff (v winner) (x b winner) (p b winner)" unfolding payoff_vector_def by simp
  also have "\<dots> = payoff (v winner) True (p b winner)" using wins by simp
  also have "\<dots> = v winner - p b winner" unfolding payoff_def by simp
  also have "\<dots> = v winner - maximum_except n b winner"
    using aa bids winner_range wins
    using allocated_implies_aa_winner
    unfolding second_price_auction_winner_def second_price_auction_winners_payment_def by simp
  finally show ?thesis by simp
qed

lemma applicant_auction_loser_payoff :
  fixes n::participants and v::real_vector and x::allocation and b::real_vector and p::payments and winner::participant and loser::participant
  assumes "applicant_auction n x p"
    and "bids n b"
    and "second_price_auction_winner n b x p winner"
    and "loser \<in> {1..n}"
    and "\<not> x b loser"
  shows "payoff_vector v (x b) (p b) loser = second_price_auction_winners_payment n b winner / (n - 1)"
proof -
  from assms not_allocated_implies_aa_loser have "applicant_auction_loser n b x p winner loser" by simp
  (* single-step "by simp" doesn't work here *)
  then show ?thesis unfolding applicant_auction_loser_def payoff_vector_def payoff_def by simp
qed

end
