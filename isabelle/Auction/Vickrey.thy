(* TODO CL: ask whether jEdit's Isabelle mode disables word wrapping *)
(* TODO CL: report Isabelle/jEdit bug: no auto-indentation *)
(* TODO CL: report Isabelle/jEdit bug: when I set long lines to wrap at window boundary, wrapped part behaves badly: not editable *)
(* TODO CL: report Isabelle/jEdit bug: can't copy goal in output pane to clipboard *)
(*
$Id$

Auction Theory Toolbox

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

header {* Vickrey's Theorem: second price auctions are
  efficient, and truthful bidding is a weakly dominant strategy *}

theory Vickrey
imports SecondPriceAuction SingleGoodAuctionProperties
begin

subsection {* Introduction *}

text{*
In second price (or Vickrey) auctions, bidders submit sealed bids;
the highest bidder wins, and pays the highest bid of the \emph{remaining} bids; the losers pay nothing.
(See \url{http://en.wikipedia.org/wiki/Vickrey_auction} for more information, including a discussion of variants used by eBay, Google and Yahoo!.)
Vickrey proved that `truth-telling' (i.e. submitting a bid equal to one's actual valuation of the good) was a weakly dominant strategy.
This means that no bidder could do strictly better by bidding above or below its valuation \emph{whatever} the other bidders did.
Thus, the auction is also efficient, awarding the item to the bidder with the highest valuation.

Vickrey was awarded Economics' Nobel prize in 1996 for his work.
High level versions of his theorem, and 12 others, were collected in Eric Maskin's 2004 review of Paul Milgrom's influential book on auction theory
(``The unity of auction theory: Milgrom's master class'', Journal of Economic Literature, 42(4), pp. 1102--1115).
Maskin himself won the Nobel in 2007.
*}


subsection {* Vickrey's Theorem *}

subsubsection {* Part 1: A second-price auction supports an equilibrium in weakly dominant strategies if all participants bid their valuation. *}

theorem vickreyA:
  fixes n :: participants and v :: "real vector" and x :: allocation and p :: payments
  assumes val: "valuation n v" and spa: "second_price_auction n x p"
  shows "equilibrium_weakly_dominant_strategy n v v (* \<leftarrow> i.e. b *) x p"
proof -
  let ?b = v
  txt {* From now on, we refer to @{term v} as @{term ?b} if we mean the \emph{bids},
    (which happen to be equal to the valuations). *}
  from val have bids: "bids n ?b" by (rule valuation_is_bid)
  from spa bids have alloc: "allocation n ?b x"
    unfolding second_price_auction_def by simp
  from spa bids have pay: "vickrey_payment n ?b p"
    unfolding second_price_auction_def by simp
  {
    fix i :: participant
    assume i_range: "i \<in> {1..n}"
    then have non_empty: "n > 0" by simp
    fix whatever_bid :: "real vector"
    assume alternative_bid: "bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i"
    then have alternative_is_bid: "bids n whatever_bid" ..
    let ?i_sticks_with_strategy = "deviation_vec n whatever_bid ?b i"
    txt {* Agent @{term i} sticks to his/her strategy (i.e. truthful bidding), whatever the others bid.
      Given this, we have to show that agent @{term i} is best off. *}
    from bids alternative_is_bid
    have i_sticks_is_bid: "bids n ?i_sticks_with_strategy"
      by (simp add: deviated_bid_well_formed)
    have weak_dominance:
      "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i \<ge>
        payoff_vector v (x whatever_bid) (p whatever_bid) i"
    proof -
      let ?b_bar = "maximum n ?b"
      show ?thesis
      proof cases -- {* case 1 of the short proof *}
        assume i_wins: "x ?i_sticks_with_strategy i"
        txt {* @{term i} gets the good, so i also satisfies the further properties of a
          second price auction winner: *}
        with spa i_sticks_is_bid i_range
        have "i \<in> arg_max_set n ?i_sticks_with_strategy"
          by (metis allocated_implies_spa_winner second_price_auction_winner_def)
        (* TODO CL: ask whether it is possible to get to "have 'a' and 'b'" directly,
           without first saying "have 'a \<and> b' and then breaking it down "by auto".
           In an earlier version we had not only deduced i_in_max_set but also the payoff here. *)
        then have "?i_sticks_with_strategy i = maximum n ?i_sticks_with_strategy"
          by (simp add: arg_max_set_def)
        also have "\<dots> \<ge> maximum_except n ?i_sticks_with_strategy i"
          using i_sticks_is_bid bids_def (* \<equiv> non_negative_real_vector n ?i_sticks_with_strategy *)
          non_empty i_range
          by (metis calculation maximum_greater_or_equal_remaining_maximum)
        finally
        have i_ge_max_except:
            "?i_sticks_with_strategy i \<ge> maximum_except n ?i_sticks_with_strategy i"
          by simp
        txt {* Now we show that @{term i}'s payoff is @{text "\<ge> 0"}. *}
        from spa i_sticks_is_bid i_range i_wins
        have winners_payoff:
          "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i =
            v i - maximum_except n ?i_sticks_with_strategy i"
          by (simp add: second_price_auction_winner_payoff)
        also have "\<dots> =
            ?i_sticks_with_strategy i - maximum_except n ?i_sticks_with_strategy i"
          unfolding deviation_vec_def deviation_def by simp
        finally have payoff_expanded:
          "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i =
            ?i_sticks_with_strategy i - maximum_except n ?i_sticks_with_strategy i"
          by simp
        (* TODO CL: ask whether/how it is possible to name one step of a calculation (for reusing it) without breaking the chain (which is what we did here) *)
        also have "\<dots> \<ge> 0" using i_ge_max_except by simp
        finally
        have non_negative_payoff:
            "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i \<ge> 0"
          by simp
        show ?thesis 
        proof cases -- {* case 1a of the short proof *}
          assume "x whatever_bid i"
          with spa alternative_is_bid non_empty i_range
          have "payoff_vector v (x whatever_bid) (p whatever_bid) i =
              v i - maximum_except n ?i_sticks_with_strategy i"
            using winners_payoff_on_deviation_from_valuation by simp
          txt {* Now we show that i's payoff hasn't changed. *}
          also have "\<dots> =
              payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i"
            using winners_payoff by simp
          finally show ?thesis by simp (* = \<longrightarrow> \<le> *)
        next -- {* case 1b of the short proof *}
          assume "\<not> x whatever_bid i"
          txt {* @{term i} doesn't get the good, so @{term i} also satisfies the further properties
            of a second price auction loser: *}
          with spa alternative_is_bid i_range
            have "payoff_vector v (x whatever_bid) (p whatever_bid) i = 0"
            by (rule second_price_auction_loser_payoff)
          also have "\<dots> \<le>
              payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i"
            using non_negative_payoff by simp
          finally show ?thesis by simp
        qed
      next -- {* case 2 of the short proof *}
        assume i_loses: "\<not> x ?i_sticks_with_strategy i"
        txt {* @{term i} doesn't get the good, so @{term i}'s payoff is @{text 0} *}
        with spa i_sticks_is_bid i_range
          have zero_payoff: "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i = 0"
          by (rule second_price_auction_loser_payoff)
        txt {* @{term i}'s bid can't be higher than the second highest bid, as otherwise
          @{term i} would have won *}
        have i_bid_at_most_second: "?i_sticks_with_strategy i \<le> maximum_except n ?i_sticks_with_strategy i"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then have "?i_sticks_with_strategy i > maximum_except n ?i_sticks_with_strategy i" by simp
          with spa i_sticks_is_bid i_range
          have "second_price_auction_winner n ?i_sticks_with_strategy x p i"
            using only_max_bidder_wins (* a lemma we had from the formalisation of the earlier 10-case proof *)
            by simp
          with i_loses show False using second_price_auction_winner_def by simp
        qed
        show ?thesis
        proof cases -- {* case 2a of the short proof *}
          assume "x whatever_bid i"
          with spa alternative_is_bid non_empty i_range
            have "payoff_vector v (x whatever_bid) (p whatever_bid) i =
              ?i_sticks_with_strategy i - maximum_except n ?i_sticks_with_strategy i"
            using winners_payoff_on_deviation_from_valuation
            by (metis deviation_vec_def deviation_def)
          txt {* Now we can compute @{term i}'s payoff *}
          also have "\<dots> \<le> 0" using i_bid_at_most_second by simp
          also have "\<dots> =
              payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i"
            using zero_payoff by simp
          finally show ?thesis by simp
        next -- {* case 2b of the short proof *}
          assume "\<not> x whatever_bid i"
          txt {* @{term i} doesn't get the good, so @{term i}'s payoff is @{text 0} *}
          with spa alternative_is_bid i_range
            have "payoff_vector v (x whatever_bid) (p whatever_bid) i = 0"
            by (rule second_price_auction_loser_payoff)
          also have "\<dots> =
              payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i"
            using zero_payoff by simp
          finally show ?thesis by simp
        qed
      qed
    qed
  }
  with spa val bids alloc pay show ?thesis
    unfolding equilibrium_weakly_dominant_strategy_def by simp
qed


subsubsection {* Part 2: A second-price auction is efficient if all participants bid their valuation. *}

(* TODO CL: document that we use local renamings (let) to make definition unfoldings resemble the original definitions *)
theorem vickreyB:
  fixes n :: participants and v :: "real vector" and x :: allocation and p :: payments
  assumes val: "valuation n v" and spa: "second_price_auction n x p"
  shows "efficient n v v x"
proof -
  let ?b = v
  from val have bids: "bids n v" by (rule valuation_is_bid)
  {
    fix k :: participant
    assume "k \<in> {1..n} \<and> x ?b k"
    with spa bids have "k \<in> arg_max_set n v"
      using allocated_implies_spa_winner second_price_auction_winner_def by simp
      (* alternative proof with fewer prerequisites (before we had the lemmas used above): *)
      (* show "k \<in> arg_max_set n v"
      proof -
        from bids and spa have
          second_price_auction_participant: "\<exists>i::participant. second_price_auction_winner n ?b x p i
                      \<and> (\<forall>j::participant. j \<in> {1..n} \<and> j \<noteq> i \<longrightarrow> second_price_auction_loser n ?b x p j)"
          unfolding second_price_auction_def by auto
        then obtain i::participant where
          i_winner: "second_price_auction_winner n ?b x p i
                      \<and> (\<forall>j::participant. j \<in> {1..n} \<and> j \<noteq> i \<longrightarrow> second_price_auction_loser n ?b x p j)" 
            by blast
        then have i_values_highest: "i \<in> arg_max_set n v" unfolding second_price_auction_winner_def by simp (* note ?b = v *)
        have k_values_highest: "k \<in> arg_max_set n v"     
        proof cases
          assume "k = i"
          with i_values_highest show ?thesis by blast
        next
          assume "k \<noteq> i"
          then show ?thesis using i_winner and k_wins by (auto simp add: second_price_auction_loser_def)
        qed
        show ?thesis using k_values_highest .
      qed *)
  }
  with bids show ?thesis using val unfolding efficient_def by blast
qed

(* unused theorems (which might nevertheless be useful for the toolbox):
   * move cursor over the word "unused_thms" for jEdit to display the list
   * This has to be at the end of the file to make sure that the whole theory has been processed. *)
unused_thms

end
