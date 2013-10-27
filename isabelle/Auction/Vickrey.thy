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

header {* Vickrey's Theorem *}

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

subsection {* Part 1: A second-price auction supports an equilibrium in weakly dominant
  strategies if all participants bid their valuation. *}

theorem vickreyA:
  fixes N::"participant set"
    and v::valuations
    and A::single_good_auction
  assumes val: "valuations N v" 
  defines "b \<equiv> v"
  assumes spa: "second_price_auction A"
      and card_N: "card N > 1"
  shows "equilibrium_weakly_dominant_strategy N v b A"
proof -
  have defined: "maximum_defined N" using card_N
    unfolding maximum_defined_def by (auto simp: card_ge_0_finite)
  then have finite: "finite N" by (metis card_N card_infinite less_nat_zero_code)

  from val have bids: "bids N b"
    unfolding b_def by (rule valuation_is_bid)
  {
    fix i :: participant
    assume i_range: "i \<in> N"

    let ?M = "N - {i}"
    have defined': "maximum_defined ?M"
      using card_N i_range unfolding maximum_defined_def
      by (simp add: card_ge_0_finite card_Diff_singleton)

    fix whatever_bid :: bids
    assume alternative_is_bid: "bids N whatever_bid"
    (* TOOD CL: also assume "whatever_bid i \<noteq> b i"? *)

    let ?b = "whatever_bid(i := b i)"
    
    have is_bid: "bids N ?b"
      using bids alternative_is_bid
      unfolding bids_def non_negative_def le_def zero_def by simp

    let ?b_max = "maximum N ?b"
    let ?b_max' = "maximum ?M ?b"

    fix x :: allocation and x' :: allocation and p :: payments and p' :: payments
    assume outcome: "((N, whatever_bid), (x, p)) \<in> A"
       and outcome': "((N, ?b), (x', p')) \<in> A"

    from spa outcome have spa_pred: "spa_pred N whatever_bid x p"
      unfolding second_price_auction_def rel_sat_sga_pred_def by blast
    from spa outcome' have spa_pred': "spa_pred N ?b x' p'"
      unfolding second_price_auction_def rel_sat_sga_pred_def by blast

    from spa_pred finite have allocation: "allocation N x" using spa_allocates by blast
    from spa_pred' finite have allocation': "allocation N x'" using spa_allocates by blast
    from spa_pred card_N have pay: "vickrey_payment N p" using spa_vickrey_payment by blast
    from spa_pred' card_N have pay': "vickrey_payment N p'" using spa_vickrey_payment by blast

    {
      assume "x i \<noteq> 1"
      with spa_pred alternative_is_bid i_range have "x i = 0"
        using spa_allocates_binary by blast
    }
    note spa_allocates_binary' = this

    have weak_dominance:
      "payoff (v i) (x' i) (p' i) \<ge> payoff (v i) (x i) (p i)"
    proof cases -- {* case 1 of the short proof *}
      assume alloc: "x' i = 1"
      with spa_pred' i_range
      have winner: "second_price_auction_winner N ?b x' p' i"
        by (rule allocated_implies_spa_winner)

      from winner have "?b i = ?b_max"
        unfolding second_price_auction_winner_def arg_max_def by simp
      with defined' have "?b i \<ge> ?b_max'"
        by (rule maximum_remaining_maximum)

      from winner have "p' i = ?b_max'"
        unfolding second_price_auction_winner_def second_price_auction_winner_outcome_def
        by simp

      have winner_payoff: "payoff (v i) (x' i) (p' i) = v i - ?b_max'"
        using defined spa_pred' i_range alloc
        by (rule second_price_auction_winner_payoff)

      have non_negative_payoff: "payoff (v i) (x' i) (p' i) \<ge> 0"
      proof -
        from `?b i \<ge> ?b_max'` have "?b i - ?b_max' \<ge> 0" by simp
        with winner_payoff show ?thesis unfolding b_def by simp
      qed

      show ?thesis
      proof cases -- {* case 1a of the short proof *}
        assume "x i = 1"
        with defined spa_pred alternative_is_bid i_range
        have "payoff (v i) (x i) (p i) = v i - ?b_max'"
          using winners_payoff_on_deviation_from_valuation unfolding b_def by simp
        also have "\<dots> = payoff (v i) (x' i) (p' i)" using winner_payoff ..
        finally show ?thesis by (rule eq_refl)
      next -- {* case 1b of the short proof *}
        assume "x i \<noteq> 1"
        then have "x i = 0" by (rule spa_allocates_binary')
        with spa_pred i_range
        have "payoff (v i) (x i) (p i) = 0"
          by (rule second_price_auction_loser_payoff)
        also have "\<dots> \<le> payoff (v i) (x' i) (p' i)" using non_negative_payoff .
        finally show ?thesis .
      qed

    next -- {* case 2 of the short proof *}
      assume non_alloc: "x' i \<noteq> 1"
      with spa_pred' i_range have "x' i = 0"
        using spa_allocates_binary by blast
      with spa_pred' i_range
      have loser_payoff: "payoff (v i) (x' i) (p' i) = 0"
        by (rule second_price_auction_loser_payoff)

      have i_bid_at_most_second: "?b i \<le> ?b_max'"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "?b i > ?b_max'" by simp
        with defined spa_pred' i_range
        have "second_price_auction_winner N ?b x' p' i"
          using only_max_bidder_wins by simp
        with non_alloc show False unfolding second_price_auction_winner_def second_price_auction_winner_outcome_def by fast
      qed

      show ?thesis
      proof cases -- {* case 2a of the short proof *}
        assume "x i = 1"
        with defined spa_pred i_range
        have "payoff (v i) (x i) (p i) = ?b i - ?b_max'"
          using winners_payoff_on_deviation_from_valuation unfolding b_def by simp
        also have "\<dots> \<le> 0" using i_bid_at_most_second by simp
        also have "\<dots> = payoff (v i) (x' i) (p' i)" using loser_payoff ..
        finally show ?thesis .
      next -- {* case 2b of the short proof *}
        assume "x i \<noteq> 1"
        then have "x i = 0" by (rule spa_allocates_binary')
        with spa_pred alternative_is_bid i_range have "x i = 0"
          using spa_allocates_binary by blast
        with spa_pred i_range
        have "payoff (v i) (x i) (p i) = 0"
          by (rule second_price_auction_loser_payoff)
        also have "\<dots> = payoff (v i) (x' i) (p' i)" using loser_payoff ..
        finally show ?thesis by (rule eq_refl)
      qed
    qed
  }
  with spa val bids show ?thesis
    using spa_is_sga
    unfolding equilibrium_weakly_dominant_strategy_def
    by auto
qed

subsection {* Part 2: A second-price auction is efficient if all participants bid their valuation. *}

theorem vickreyB:
  fixes N :: "participant set" and v :: valuations and A :: single_good_auction
  assumes val: "valuations N v"
  assumes spa: "second_price_auction A"
  defines "b \<equiv> v"
  shows "efficient N v b A"
proof -
  from val have bids: "bids N v" by (rule valuation_is_bid)
  {
    fix k :: participant and x :: allocation and p :: payments
    (* TODO CL: We actually don't need p; is there a way to do without naming it? *)
    assume range: "k \<in> N" and outcome: "((N, v), (x, p)) \<in> A" and wins: "x k = 1"
    from outcome spa have "spa_pred N v x p"
      unfolding second_price_auction_def rel_sat_sga_pred_def
      by blast
    with range and wins have "k \<in> arg_max N v"
      using allocated_implies_spa_winner
      unfolding second_price_auction_winner_def by blast
  }
  with bids spa show ?thesis
    using val unfolding b_def efficient_def using spa_is_sga by blast
qed

end
