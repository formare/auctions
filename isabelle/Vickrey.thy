(* TODO CL: ask whether jEdit's Isabelle mode disables word wrapping *)
(* TODO CL: report Isabelle/jEdit bug: no auto-indentation *)
(* TODO CL: report Isabelle/jEdit bug: when I set long lines to wrap at window boundary, wrapped part behaves badly: not editable *)
(* TODO CL: report Isabelle/jEdit bug: can't copy goal in output pane to clipboard *)
header {* Vickrey's Theorem:
Second price auctions support an equilibrium in weakly dominant strategies, and are efficient, if each participant bids their valuation of the good. *}

(*
$Id$

Auction Theory Toolbox

Authors:
* Manfred Kerber <m.kerber@cs.bham.ac.uk>
* Christoph Lange <c.lange@cs.bham.ac.uk>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory Vickrey
imports SingleGoodAuction Maximum

begin

section{* Introduction *}

text{*
In second price (or Vickrey) auctions, bidders submit sealed bids;
the highest bidder wins, and pays the highest bid of the \emph{remaining} bids; the losers pay nothing.
(See \url{http://en.wikipedia.org/wiki/Vickrey_auction} for more information, including a discussion of variants used by eBay, Google and Yahoo!.)
Vickrey proved that `truth-telling' (i.e. submitting a bid equal to one's actual valuation of the good) was a weakly dominant strategy.
This means that no bidder could do strictly better by bidding above or below its valuation \emph{whatever} the other bidders did.
Thus, the auction is also efficient, awarding the item to the bidder with the highest valuation.

Vickrey was awarded Economics' Nobel prize in 1996 for his work.
High level versions of his theorem, and 12 others, were collected in Eric Maskin's 2004 review of Paul Milgrom's influential book on auction theory
("The unity of auction theory: Milgrom's master class", Journal of Economic Literature, 42(4), pp. 1102–1115).
Maskin himself won the Nobel in 2007.
*}

section{* Second-price auction *}

text{* Agent i being the winner of a second-price auction (see below for complete definition) means
* he/she is one of the participants with the highest bids
* he/she wins the auction
* and pays the maximum price that remains after removing the winner's own bid from the vector of bids. *}
definition second_price_auction_winner ::
  "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool" where
  "second_price_auction_winner n b x p i \<equiv> i \<in> {1..n} \<and> i \<in> arg_max_set n b \<and> x b i \<and> (p b i = maximum_except n b i)"

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
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and winner: "second_price_auction_winner n b x p winner"
    and also_winner: "second_price_auction_winner n b x p j"
  shows "j = winner"
  using assms
  unfolding second_price_auction_def second_price_auction_winner_def
  using allocation_unique
  by blast

text{* The participant who gets the good also satisfies the further properties of a second-price auction winner *}
lemma allocated_implies_spa_winner :
  fixes n::participants and x::allocation and p::payments and b::real_vector and winner::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and winner_range: "winner \<in> {1..n}"  (* in an earlier version we managed without this assumption, but it makes the proof easier *)
    and wins: "x b winner"
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
    unfolding second_price_auction_winner_def by simp
  finally show ?thesis by simp
qed

text{* a formula for computing the payoff of a loser of a second-price auction *}
lemma second_price_auction_loser_payoff :
  fixes n::participants and v::real_vector and x::allocation and b::real_vector and p::payments and loser::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "loser \<in> {1..n}"
    and loses: "\<not> x b loser"
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
proof -
  let ?winner_sticks_with_valuation = "deviation_vec n b v winner"
  (* winner gets the good, so winner also satisfies the further properties of a second price auction winner: *)
  from wins range spa bids
    have "payoff_vector v (x b) (p b) winner = v winner - maximum_except n b winner"
    by (simp add: second_price_auction_winner_payoff)
  (* i's deviation doesn't change the maximum remaining bid (which is the second highest bid when winner wins) *)
  also have "\<dots> = v winner - maximum_except n ?winner_sticks_with_valuation winner"
    unfolding deviation_vec_def using non_empty range remaining_maximum_invariant by simp
  finally show ?thesis by simp
qed

section{* Efficiency *}

text{* A single good auction (this is the one we are talking about here) is efficient, if the winner is among the participants who have the
highest valuation of the good. *}
definition efficient ::
  "participants \<Rightarrow> real_vector \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> bool" where
  "efficient n v b x \<equiv> (valuation n v \<and> bids n b) \<and>
      (\<forall>i::participant. i \<in> {1..n} \<and> x b i \<longrightarrow> i \<in> arg_max_set n v)"

section{* Equilibrium in weakly dominant strategies *}

text{* Given some auction, a strategy profile supports an equilibrium in weakly dominant strategies
  if each participant maximises its payoff by playing its component in that profile,
    whatever the other participants do. *}
definition equilibrium_weakly_dominant_strategy ::
  "participants \<Rightarrow> real_vector \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool" where
  "equilibrium_weakly_dominant_strategy n v b x p \<equiv>
    (* TODO CL: note that 'bids n b' is actually redundant, as allocation and vickrey_payment require bids. *)
    valuation n v \<and> bids n b \<and> allocation n b x \<and> vickrey_payment n b p \<and> 
   (\<forall> i::participant . i \<in> {1..n} \<longrightarrow>
     (\<forall> whatever_bid::real_vector . bids n whatever_bid \<and> whatever_bid i \<noteq> b i \<longrightarrow> (
       let i_sticks_with_bid = deviation_vec n whatever_bid b i (* here, all components are (whatever_bid j), just the i-th component remains (b i) *)
       in payoff_vector v (x i_sticks_with_bid) (p i_sticks_with_bid) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i)))"

(* TODO CL: discuss whether we should define _dominant_ in addition to _weakly_ dominant.  If so, can we refactor the definitions in some way that makes this less redundant? *)

section{* Vickrey's Theorem *}

subsection{* Part 1: A second-price auction supports an equilibrium in weakly dominant strategies if all participants bid their valuation. *}
theorem vickreyA :
  fixes n::participants and v::real_vector and x::allocation and p::payments
  assumes val: "valuation n v" and spa: "second_price_auction n x p"
  shows "equilibrium_weakly_dominant_strategy n v v (* \<leftarrow> i.e. b *) x p"
proof -
  let ?b = v (* From now on, we refer to v as ?b if we mean the _bids_ (which happen to be equal to the valuations) *)
  from val have bids: "bids n ?b" by (rule valuation_is_bid)
  from spa bids have alloc: "allocation n ?b x" unfolding second_price_auction_def by simp
  from spa bids have pay: "vickrey_payment n ?b p" unfolding second_price_auction_def by simp
  {
    fix i::participant
    assume i_range: "i \<in> {1..n}"
    fix whatever_bid::real_vector
    assume alternative_bid: "bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i"
    then have alternative_is_bid: "bids n whatever_bid" ..
    let ?i_sticks_with_valuation = "deviation_vec n whatever_bid ?b i"
      (* Agent i sticks to bidding his/her valuation, whatever the others bid.  Given this, we have to show that agent i is best off. *)
    from bids alternative_is_bid
      have i_sticks_is_bid: "bids n ?i_sticks_with_valuation"
      by (simp add: deviated_bid_well_formed)
    have weak_dominance: "payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i"
    proof (cases "n = 0")
      case True
      with i_range show ?thesis by simp
    next                 
      case False
      then have non_empty: "n > 0" ..
      let ?b_bar = "maximum n ?b"
      show ?thesis
      proof cases (* case 1 of the short proof *)
        assume i_wins: "x ?i_sticks_with_valuation i"
        (* i gets the good, so i also satisfies the further properties of a second price auction winner: *)
        with spa i_sticks_is_bid i_range
          have "i \<in> arg_max_set n ?i_sticks_with_valuation" by (metis allocated_implies_spa_winner second_price_auction_winner_def)
        (* TODO CL: ask whether it is possible to get to "have 'a' and 'b'" directly,
           without first saying "have 'a \<and> b' and then breaking it down "by auto".
           In an earlier version we had not only deduced i_in_max_set but also the payoff here. *)
        then have "?i_sticks_with_valuation i = maximum n ?i_sticks_with_valuation" by (simp add: arg_max_set_def)
        also have "\<dots> \<ge> maximum_except n ?i_sticks_with_valuation i"
          using i_sticks_is_bid bids_def (* \<equiv> non_negative_real_vector n ?i_sticks_with_valuation *)
          non_empty i_range
          by (metis calculation maximum_greater_or_equal_remaining_maximum)
        finally have i_ge_max_except: "?i_sticks_with_valuation i \<ge> maximum_except n ?i_sticks_with_valuation i" by simp
        (* Now we show that i's payoff is \<ge> 0 *)
        from spa i_sticks_is_bid i_range i_wins have "payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i
          = v i - maximum_except n ?i_sticks_with_valuation i" by (simp add: second_price_auction_winner_payoff)
        also have "\<dots> = ?i_sticks_with_valuation i - maximum_except n ?i_sticks_with_valuation i"
          unfolding deviation_vec_def deviation_def by simp
        finally have payoff_expanded: "payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i =
          ?i_sticks_with_valuation i - maximum_except n ?i_sticks_with_valuation i" by simp
        (* TODO CL: ask whether/how it is possible to name one step of a calculation (for reusing it) without breaking the chain (which is what we did here) *)
        also have "... \<ge> 0" using i_ge_max_except by simp
        finally have non_negative_payoff: "payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i \<ge> 0" by simp
        show ?thesis  
        proof cases (* case 1a of the short proof *)
          assume "x whatever_bid i"
          with spa alternative_is_bid non_empty i_range
            have "payoff_vector v (x whatever_bid) (p whatever_bid) i = ?i_sticks_with_valuation i - maximum_except n ?i_sticks_with_valuation i"
            using winners_payoff_on_deviation_from_valuation by (metis deviation_vec_def deviation_def)
          (* Now we show that i's payoff hasn't changed *)
          also have "\<dots> = payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i"
            using payoff_expanded by simp
          finally show ?thesis by simp (* = \<longrightarrow> \<le> *)
        next (* case 1b of the short proof *)
          assume "\<not> x whatever_bid i"
          (* i doesn't get the good, so i also satisfies the further properties of a second price auction loser: *)
          with spa alternative_is_bid i_range
            have "payoff_vector v (x whatever_bid) (p whatever_bid) i = 0"
            by (rule second_price_auction_loser_payoff)
          also have "\<dots> \<le> payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i" using non_negative_payoff by simp
          finally show ?thesis by simp
        qed
      next (* case 2 of the short proof *)
        assume i_loses: "\<not> x ?i_sticks_with_valuation i"
        (* i doesn't get the good, so i's payoff is 0 *)
        with spa i_sticks_is_bid i_range
          have zero_payoff: "payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i = 0"
          by (rule second_price_auction_loser_payoff)
        (* i's bid can't be higher than the second highest bid, as otherwise i would have won *)
        have i_bid_at_most_second: "?i_sticks_with_valuation i \<le> maximum_except n ?i_sticks_with_valuation i"
        proof - (* by contradiction *)
          {
            assume "\<not> ?i_sticks_with_valuation i \<le> maximum_except n ?i_sticks_with_valuation i"
            then have "?i_sticks_with_valuation i > maximum_except n ?i_sticks_with_valuation i" by simp
            with spa i_sticks_is_bid i_range
              have "second_price_auction_winner n ?i_sticks_with_valuation x p i"
              using only_max_bidder_wins (* a lemma we had from the formalisation of the earlier 10-case proof *)
              by simp
            with i_loses have False using second_price_auction_winner_def by simp
          }
          then show ?thesis by blast
        qed
        show ?thesis
        proof cases (* case 2a of the short proof *)
          assume "x whatever_bid i"
          with spa alternative_is_bid non_empty i_range
            have "payoff_vector v (x whatever_bid) (p whatever_bid) i = ?i_sticks_with_valuation i - maximum_except n ?i_sticks_with_valuation i"
            using winners_payoff_on_deviation_from_valuation by (metis deviation_vec_def deviation_def)
          (* Now we can compute i's payoff *)
          also have "\<dots> \<le> 0" using i_bid_at_most_second by simp
          also have "\<dots> = payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i"
            using zero_payoff by simp
          finally show ?thesis by simp
        next (* case 2b of the short proof *)
          assume "\<not> x whatever_bid i"
          (* i doesn't get the good, so i's payoff is 0 *)
          with spa alternative_is_bid i_range
            have "payoff_vector v (x whatever_bid) (p whatever_bid) i = 0"
            by (rule second_price_auction_loser_payoff)
          also have "\<dots> = payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i" using zero_payoff by simp
          finally show ?thesis by simp
        qed
      qed
    qed
  }
  with spa val bids alloc pay show ?thesis unfolding equilibrium_weakly_dominant_strategy_def by simp
qed

subsection{* Part 2: A second-price auction is efficient if all participants bid their valuation. *}
(* TODO CL: document that we use local renamings (let) to make definition unfoldings resemble the original definitions *)
theorem vickreyB :
  fixes n::participants and v::real_vector and x::allocation and p::payments
  assumes val: "valuation n v" and spa: "second_price_auction n x p"
  shows "efficient n v v x"
proof -
  let ?b = v
  from val have bids: "bids n v" by (rule valuation_is_bid)
  {
    fix k:: participant
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
