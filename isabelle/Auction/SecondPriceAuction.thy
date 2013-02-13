(*
$Id$

Auction Theory Toolbox

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

theory SecondPriceAuction
imports SingleGoodAuction Maximum

begin

section{* Second-price auction *}

text{* Agent i being the winner of a second-price auction (see below for complete definition) means
* he/she is one of the participants with the highest bids
* he/she wins the auction
* and pays the maximum price that remains after removing the winner's own bid from the vector of bids. *}
definition second_price_auction_winners_payment :: "participants \<Rightarrow> real_vector \<Rightarrow> participant \<Rightarrow> real"
  where "second_price_auction_winners_payment n b winner \<equiv> maximum_except n b winner"

definition second_price_auction_winner ::
  "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool" where
  "second_price_auction_winner n b x p i \<equiv> i \<in> {1..n} \<and> i \<in> arg_max_set n b \<and> x b i 
                                           \<and> (p b i = second_price_auction_winners_payment n b i)"

text{* Agent i being a loser of a second-price auction (see below for complete definition) means
* he/she loses the auction
* and pays nothing *}
definition second_price_auction_loser ::
  "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool" where
  "second_price_auction_loser n b x p i \<equiv> i \<in> {1..n} \<and> \<not>x b i \<and> p b i = 0"

text{* A second-price auction is an auction whose outcome satisfies the following conditions:
1. One of the participants with the highest bids wins. (We do not formalise the random selection of one distinct participants from the set of highest bidders,
in case there is more than one.)
2. The price that the winner pays is the maximum bid that remains after removing the winner's own bid from the vector of bids.
3. The losers do not pay anything. *}
definition second_price_auction ::
  "participants \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool" where
  "second_price_auction n x p \<equiv>
    \<forall> b::real_vector . bids n b \<longrightarrow> allocation n b x \<and> vickrey_payment n b p \<and>
    (\<exists>i::participant . i \<in> {1..n} \<and> second_price_auction_winner n b x p i
                      \<and> (\<forall>j::participant . j \<in> {1..n} \<and> j \<noteq> i \<longrightarrow> second_price_auction_loser n b x p j))"

text{* We chose not to \emph{define} that a second-price auction has only one winner, as it is not necessary.  Therefore we have to prove it. *}
(* TODO CL: discuss whether it makes sense to keep this lemma – it's not used for "theorem vickreyA" but might still be useful for the toolbox *)
lemma second_price_auction_has_only_one_winner :
  fixes n::participants and x::allocation and p::payments and b::real_vector and winner::participant and j::participant
  assumes "second_price_auction n x p"
    and "bids n b"
    and "second_price_auction_winner n b x p winner"
    and "second_price_auction_winner n b x p j"
  shows "j = winner"
  using assms
  unfolding second_price_auction_def second_price_auction_winner_def
  using allocation_unique
  by blast

text{* The participant who gets the good also satisfies the further properties of a second-price auction winner *}
lemma allocated_implies_spa_winner :
  fixes n::participants and x::allocation and p::payments and b::real_vector and winner::participant
  assumes "second_price_auction n x p"
    and "bids n b"
    and "winner \<in> {1..n}"  (* in an earlier version we managed without this assumption, but it makes the proof easier *)
    and "x b winner"
  shows "second_price_auction_winner n b x p winner"
  using assms
  unfolding second_price_auction_def second_price_auction_winner_def
  using allocation_unique
  by blast

text{* A participant who doesn't gets the good satisfies the further properties of a second-price auction loser *}
lemma not_allocated_implies_spa_loser :
  fixes n::participants and x::allocation and p::payments and b::real_vector and loser::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "loser \<in> {1..n}"
    and loses: "\<not> x b loser"
  shows "second_price_auction_loser n b x p loser"
proof - (* by contradiction *)
  {
    assume False: "\<not> second_price_auction_loser n b x p loser"
    have "x b loser"
      using second_price_auction_def
      using spa bids
      using False range
      using second_price_auction_winner_def by auto
    with loses have "False" ..
  }
  then show ?thesis by blast
qed

text{* If there is only one bidder with a maximum bid, that bidder wins. *}
lemma only_max_bidder_wins :
  fixes n::participants and max_bidder::participant and b::real_vector and x::allocation and p::payments
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "max_bidder \<in> {1..n}"
    (* and max_bidder: "b max_bidder = maximum n b" *) (* we actually don't need this :-) *)
    and only_max_bidder: "b max_bidder > maximum_except n b max_bidder"
  shows "second_price_auction_winner n b x p max_bidder"
proof -
  from bids spa have spa_unfolded: "\<exists>i::participant. second_price_auction_winner n b x p i
    \<and> (\<forall>j::participant. j \<in> {1..n} \<and> j \<noteq> i \<longrightarrow> second_price_auction_loser n b x p j)"
    unfolding second_price_auction_def by blast
  then have x_is_allocation: "\<exists>i:: participant. i \<in> {1..n} \<and> x b i \<and> (\<forall>j:: participant. j \<in> {1..n} \<and> j\<noteq>i \<longrightarrow> \<not>x b j)"
    unfolding second_price_auction_winner_def second_price_auction_loser_def by blast
  {
    fix j::participant
    assume j_not_max: "j \<in> {1..n} \<and> j \<noteq> max_bidder"
    have "j \<notin> arg_max_set n b"
    proof -
      from j_not_max range have "b j \<le> maximum_except n b max_bidder"
        using maximum_except_is_greater_or_equal by simp
      with only_max_bidder have b_j_lt_max: "b j < b max_bidder" by simp
      then show ?thesis
      proof - (* by contradiction *)
        {
          assume "b j = maximum n b"
            with range have "b j \<ge> b max_bidder" by (simp add: maximum_is_greater_or_equal)
          with b_j_lt_max have False by simp
        }
        then show ?thesis unfolding arg_max_set_def
          by (metis (lifting, full_types) mem_Collect_eq)
          (* recommended by sledgehammer using e *)
      qed
    qed
  }
  with (* max_bidder *) (* turns out that we didn't need this :-) *)
    x_is_allocation spa_unfolded show ?thesis by (metis second_price_auction_winner_def)
qed

text{* a formula for computing the payoff of the winner of a second-price auction *}
lemma second_price_auction_winner_payoff :
  fixes n::participants and v::real_vector and x::allocation and b::real_vector and p::payments and winner::participant
  assumes spa: "second_price_auction n x p"
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
    using spa bids winner_range wins
    using allocated_implies_spa_winner
    unfolding second_price_auction_winner_def second_price_auction_winners_payment_def by simp
  finally show ?thesis by simp
qed

text{* a formula for computing the payoff of a loser of a second-price auction *}
lemma second_price_auction_loser_payoff :
  fixes n::participants and v::real_vector and x::allocation and b::real_vector and p::payments and loser::participant
  assumes "second_price_auction n x p"
    and "bids n b"
    and "loser \<in> {1..n}"
    and "\<not> x b loser"
  shows "payoff_vector v (x b) (p b) loser = 0"
  using assms not_allocated_implies_spa_loser
  unfolding second_price_auction_loser_def payoff_vector_def payoff_def by simp

text{* If a participant wins a second-price auction by not bidding his/her valuation,
  the payoff equals the valuation minus the remaining maximum bid *}
lemma winners_payoff_on_deviation_from_valuation :
  fixes n::participants and v::real_vector and x::allocation and b::real_vector and p::payments and winner::participant
  (* how this was created by factoring out stuff from vickreyA proof cases 1a and 2a:
     1. wrote "lemma \<dots> fixes \<dots> shows
     2. pasted proof steps
     3. added assumptions as needed *)
  assumes non_empty: "n > 0"
    and spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "winner \<in> {1..n}"
    and wins: "x b winner"
  shows "let winner_sticks_with_valuation = deviation_vec n b v winner
    in payoff_vector v (x b) (p b) winner = v winner - maximum_except n winner_sticks_with_valuation winner"
  using wins range spa bids second_price_auction_winner_payoff (* compute the winner's payoff *)
  unfolding deviation_vec_def (* unfold to deviation, as remaining_maximum_invariant is stated for elements not vectors *)
  (* i's deviation doesn't change the maximum remaining bid (which is the second highest bid when winner wins) *)
  using non_empty remaining_maximum_invariant
  by simp
(* Until the CASL formalisation made us realise how easy eprover could prove this, we had been using the following structured proof: *)
(* proof -
  let ?winner_sticks_with_valuation = "deviation_vec n b v winner"
  (* winner gets the good, so winner also satisfies the further properties of a second price auction winner: *)
  from wins range spa bids
    have "payoff_vector v (x b) (p b) winner = v winner - maximum_except n b winner"
    by (simp add: second_price_auction_winner_payoff)
  (* i's deviation doesn't change the maximum remaining bid (which is the second highest bid when winner wins) *)
  also have "\<dots> = v winner - maximum_except n ?winner_sticks_with_valuation winner"
    unfolding deviation_vec_def using non_empty range remaining_maximum_invariant by simp
  finally show ?thesis by simp
qed *)

(* unused theorems (which might nevertheless be useful for the toolbox):
   * move cursor over the word "unused_thms" for jEdit to display the list
   * This has to be at the end of the file to make sure that the whole theory has been processed. *)
unused_thms

end
