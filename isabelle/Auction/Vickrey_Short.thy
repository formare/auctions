(*
$Id: Vickrey_Short.thy 423 2013-02-16 16:58:12Z makarius $

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

theory Vickrey_Short
imports Complex_Main
begin

section {* Single good auctions *}

subsection {* Preliminaries *}

type_synonym participant = nat
type_synonym participants = "nat set"

type_synonym 'a vector = "participant \<Rightarrow> 'a"

definition non_negative_real_vector :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "non_negative_real_vector N v \<longleftrightarrow> (\<forall>i \<in> N. v i \<ge> 0)"

definition positive_real_vector :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "positive_real_vector N v \<longleftrightarrow> (\<forall>i \<in> N. v i > 0)"

type_synonym allocation = "real vector \<Rightarrow> participant \<Rightarrow> bool"
type_synonym payments = "real vector \<Rightarrow> participant \<Rightarrow> real"


subsection {* Strategy (bids) *}

definition bids :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "bids N b \<longleftrightarrow> non_negative_real_vector N b"


subsection {* Allocation *}

definition allocation :: "participants \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> bool"
  where "allocation N b x \<longleftrightarrow> bids N b \<and> (\<exists>!i \<in> N. x b i)"


subsection {* Payment *}

definition vickrey_payment :: "participants \<Rightarrow> real vector \<Rightarrow> payments \<Rightarrow> bool"
  where "vickrey_payment N b p \<longleftrightarrow> bids N b \<and> (\<forall>i \<in> N. p b i \<ge> 0)"


subsection {* Valuation *}

definition valuation :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "valuation N v \<longleftrightarrow> positive_real_vector N v"

lemma valuation_is_bid: "valuation N v \<Longrightarrow> bids N v"
  unfolding valuation_def positive_real_vector_def
  unfolding bids_def non_negative_real_vector_def
  by auto


subsection {* Payoff *}

definition payoff :: "real \<Rightarrow> bool \<Rightarrow> real \<Rightarrow> real"
  where "payoff v x p = v * (if x then 1 else 0) - p"


subsection {* Maximum *}

definition maximum_defined :: "participants \<Rightarrow> bool"
  where "maximum_defined N \<longleftrightarrow> card N > 0"

definition maximum :: "participants \<Rightarrow> real vector \<Rightarrow> real"
  where "maximum N y = Max (y ` N)"

lemma maximum_equal:
  fixes N :: participants and y :: "real vector" and z :: "real vector"
  assumes "\<forall>i \<in> N. y i = z i"
  shows "maximum N y = maximum N z"
proof -
  have "y ` N = z ` N" by (rule image_cong) (auto simp add: assms)
  then show ?thesis unfolding maximum_def by simp
qed

lemma maximum_is_greater_or_equal:
  fixes N :: participants and y :: "real vector" and i :: participant
  assumes "maximum_defined N"
    and "i \<in> N"
  shows "maximum N y \<ge> y i"
  using assms unfolding maximum_defined_def maximum_def by (simp add: card_gt_0_iff)

lemma maximum_is_component:
  fixes N :: participants and y :: "real vector"
  assumes defined: "maximum_defined N"
    and non_negative: "non_negative_real_vector N y"
  shows "\<exists>i \<in> N. maximum N y = y i"
proof -
  let ?A = "y ` N"
  from defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (simp_all add: card_gt_0_iff)
  then have "Max ?A \<in> ?A" by (rule Max_in)
  then obtain i where "i \<in> N" and "Max ?A = y i" by auto
  with maximum_def show ?thesis by auto
qed

lemma maximum_sufficient:
  fixes N :: participants and y :: "real vector" and m :: real
  assumes non_negative: "non_negative_real_vector N y"
    and defined: "maximum_defined N"
    and greater_or_equal: "\<forall>i \<in> N. m \<ge> y i"
    and is_component: "\<exists>i \<in> N. m = y i"
  shows "maximum N y = m"
  unfolding maximum_def
proof -
  let ?A = "y ` N"
  show "Max ?A = m"
  proof (rule Max_eqI)
    from defined show "finite ?A"
      unfolding maximum_defined_def by (simp add: card_gt_0_iff)
    show "m \<in> ?A" using is_component by auto
    fix a assume "a \<in> ?A"
    then show "a \<le> m" using greater_or_equal by blast
  qed
qed

definition arg_max_set :: "participants \<Rightarrow> real vector \<Rightarrow> participants"
  where "arg_max_set N b = {i. i \<in> N \<and> maximum N b = b i}"

lemma maximum_except_is_greater_or_equal:
  fixes N :: participants and y :: "real vector" and j :: participant and i :: participant
  assumes defined: "maximum_defined N"
    and i: "i \<in> N \<and> i \<noteq> j"
  shows "maximum (N - {j}) y \<ge> y i"
proof -
  let ?M = "N - {j}"
  let ?A = "y ` ?M"
  from i have *: "i \<in> ?M" by simp
  with defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (auto simp add: card_gt_0_iff)
  with * have "Max ?A \<ge> y i" by (auto simp add: Max_ge_iff)
  then show ?thesis unfolding maximum_def .
qed

lemma maximum_remaining_maximum:
  fixes N :: participants and y :: "real vector" and j :: participant
  assumes defined': "maximum_defined (N - {j})"
    and j_max: "y j = maximum N y"
  shows "y j \<ge> maximum (N - {j}) y"
proof -
  have "y ` (N - {j}) \<subseteq> y ` N" by auto
  with defined' have "maximum (N - {j}) y \<le> maximum N y"
    unfolding maximum_def maximum_defined_def by (simp add: card_gt_0_iff Max_mono)
  also note j_max [symmetric]
  finally show ?thesis .
qed

lemma remaining_maximum_invariant:
  fixes N :: participants and y :: "real vector" and i :: participant and a :: real
  shows "maximum (N - {i}) (y(i := a)) = maximum (N - {i}) y"
proof -
  let ?M = "N - {i}"
  have "y ` ?M = (y(i := a)) ` ?M" by auto
  then show ?thesis unfolding maximum_def by simp
qed


subsection {* Second price single good auctions and some of their properties *}

definition second_price_auction_winners_payment ::
    "participants \<Rightarrow> real vector \<Rightarrow> participant \<Rightarrow> real"
  where "second_price_auction_winners_payment N b winner = maximum (N - {winner}) b"

definition second_price_auction_winner ::
    "participants \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where
    "second_price_auction_winner N b x p i \<longleftrightarrow>
      i \<in> N \<and> i \<in> arg_max_set N b \<and> x b i \<and> p b i = second_price_auction_winners_payment N b i"

definition second_price_auction_loser ::
    "participants \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where "second_price_auction_loser N b x p i \<longleftrightarrow> i \<in> N \<and> \<not> x b i \<and> p b i = 0"

definition second_price_auction :: "participants \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "second_price_auction N x p \<longleftrightarrow>
      (\<forall>b. bids N b \<longrightarrow>
        allocation N b x \<and> vickrey_payment N b p \<and>
        (\<exists>i \<in> N. second_price_auction_winner N b x p i \<and>
          (\<forall>j \<in> N. j \<noteq> i \<longrightarrow> second_price_auction_loser N b x p j)))"

lemma allocated_implies_spa_winner:
  fixes N :: participants and x :: allocation and p :: payments
    and b :: "real vector" and winner :: participant
  assumes "second_price_auction N x p"
    and "bids N b"
    and "winner \<in> N"
    and "x b winner"
  shows "second_price_auction_winner N b x p winner"
  using assms
  unfolding second_price_auction_def second_price_auction_winner_def allocation_def
  by blast

lemma not_allocated_implies_spa_loser:
  fixes N :: participants and x :: allocation and p :: payments
    and b :: "real vector" and loser :: participant
  assumes spa: "second_price_auction N x p"
    and bids: "bids N b"
    and range: "loser \<in> N"
    and loses: "\<not> x b loser"
  shows "second_price_auction_loser N b x p loser"
proof -
  from loses have "\<not> second_price_auction_winner N b x p loser"
    unfolding second_price_auction_winner_def by simp
  with spa bids range show ?thesis
    unfolding second_price_auction_def by auto
qed

lemma only_max_bidder_wins:
  fixes N :: participants and max_bidder :: participant
    and b :: "real vector" and x :: allocation and p :: payments
  assumes defined: "maximum_defined N"
    and spa: "second_price_auction N x p"
    and bids: "bids N b"
    and range: "max_bidder \<in> N"
    and only_max_bidder: "b max_bidder > maximum (N - {max_bidder}) b"
  shows "second_price_auction_winner N b x p max_bidder"
proof -
  from spa bids have spa_unfolded:
    "\<exists>i. second_price_auction_winner N b x p i \<and>
      (\<forall>j \<in> N. j \<noteq> i \<longrightarrow> second_price_auction_loser N b x p j)"
    unfolding second_price_auction_def by blast
  {
    fix j :: participant
    assume j_not_max: "j \<in> N \<and> j \<noteq> max_bidder"
    have "j \<notin> arg_max_set N b"
    proof
      assume "j \<in> arg_max_set N b"
      then have maximum: "b j = maximum N b" unfolding arg_max_set_def by simp

      from j_not_max range have "b j \<le> maximum (N - {max_bidder}) b"
        using defined maximum_except_is_greater_or_equal by simp
      with only_max_bidder have *: "b j < b max_bidder" by simp

      from defined range maximum have "b j \<ge> b max_bidder"
        by (simp add: maximum_is_greater_or_equal)
      with * show False by simp
    qed
  }
  with spa_unfolded show ?thesis
    by (auto simp add: second_price_auction_winner_def)
qed

lemma second_price_auction_winner_payoff:
  fixes N :: participants and v :: "real vector" and x :: allocation
    and b :: "real vector" and p :: payments and winner :: participant
  assumes defined: "maximum_defined N"
    and spa: "second_price_auction N x p"
    and bids: "bids N b"
    and i_range: "i \<in> N"
    and wins: "x b i"
  shows "payoff (v i) (x b i) (p b i) = v i - maximum (N - {i}) b"
proof -
  have "payoff (v i) (x b i) (p b i) = v i - p b i"
    using wins unfolding payoff_def by simp
  also have "\<dots> = v i - maximum (N - {i}) b"
    using defined spa bids i_range wins
    using allocated_implies_spa_winner
    unfolding second_price_auction_winner_def second_price_auction_winners_payment_def
    by simp
  finally show ?thesis .
qed

lemma second_price_auction_loser_payoff:
  fixes N :: participants and v :: "real vector" and x :: allocation
    and b :: "real vector" and p :: payments and loser :: participant
  assumes "second_price_auction N x p"
    and "bids N b"
    and "i \<in> N"
    and "\<not> x b i"
  shows "payoff (v i) (x b i) (p b i) = 0"
  using assms not_allocated_implies_spa_loser
  unfolding second_price_auction_loser_def payoff_def by simp

lemma winners_payoff_on_deviation_from_valuation:
  fixes N :: participants and v :: "real vector" and x :: allocation
    and b :: "real vector" and p :: payments and winner :: participant
  assumes "maximum_defined N"
    and "second_price_auction N x p"
    and "bids N b"
    and "i \<in> N"
    and "x b i"
  shows "payoff (v i) (x b i) (p b i) = v i - maximum (N - {i}) (b(i := v i))"
  using assms second_price_auction_winner_payoff remaining_maximum_invariant
  by simp


section {* Some properties that single good auctions can have *}

subsection {* Efficiency *}

definition efficient :: "participants \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> bool"
  where
    "efficient N v b x \<longleftrightarrow>
      valuation N v \<and> bids N b \<and> (\<forall>i \<in> N. x b i \<longrightarrow> i \<in> arg_max_set N v)"


subsection {* Equilibrium in weakly dominant strategies *}

definition equilibrium_weakly_dominant_strategy ::
  "participants \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool" where
  "equilibrium_weakly_dominant_strategy N v b x p \<longleftrightarrow>
    valuation N v \<and> bids N b \<and> allocation N b x \<and> vickrey_payment N b p \<and>
    (\<forall>i \<in> N.
      (\<forall>whatever_bid. bids N whatever_bid \<and> whatever_bid i \<noteq> b i \<longrightarrow>
        (let b' = whatever_bid(i := b i)
         in payoff (v i) (x b' i) (p b' i) \<ge>
            payoff (v i) (x whatever_bid i) (p whatever_bid i))))"


section {* Vickrey's Theorem *}

subsection {* Part 1: A second-price auction supports an equilibrium in weakly dominant
  strategies if all participants bid their valuation. *}

theorem vickreyA:
  fixes N :: participants and v :: "real vector" and x :: allocation and p :: payments
  assumes card_N: "card N > 1"
  assumes val: "valuation N v" and spa: "second_price_auction N x p"
  defines "b \<equiv> v"
  shows "equilibrium_weakly_dominant_strategy N v b x p"
proof -
  have defined: "maximum_defined N" using card_N
    unfolding maximum_defined_def by (auto simp: card_ge_0_finite)

  from val have bids: "bids N b"
    unfolding b_def by (rule valuation_is_bid)
  from spa bids have allocation: "allocation N b x"
    unfolding b_def second_price_auction_def by simp
  from spa bids have pay: "vickrey_payment N b p"
    unfolding b_def second_price_auction_def by simp
  {
    fix i :: participant
    assume i_range: "i \<in> N"

    let ?M = "N - {i}"
    have defined': "maximum_defined ?M"
      using card_N i_range unfolding maximum_defined_def
      by (simp add: card_ge_0_finite card_Diff_singleton)

    fix whatever_bid :: "real vector"
    assume alternative_is_bid: "bids N whatever_bid"

    let ?b = "whatever_bid(i := b i)"
    
    have is_bid: "bids N ?b"
      using bids alternative_is_bid
      unfolding bids_def non_negative_real_vector_def by simp

    let ?b_max = "maximum N ?b"
    let ?b_max' = "maximum ?M ?b"

    have weak_dominance:
      "payoff (v i) (x ?b i) (p ?b i) \<ge> payoff (v i) (x whatever_bid i) (p whatever_bid i)"
    proof cases
      assume alloc: "x ?b i"
      with spa is_bid i_range
      have winner: "second_price_auction_winner N ?b x p i"
        by (rule allocated_implies_spa_winner)

      from winner have "?b i = ?b_max"
        unfolding second_price_auction_winner_def arg_max_set_def by simp
      with defined' have "?b i \<ge> ?b_max'"
        by (rule maximum_remaining_maximum)

      from winner have "p ?b i = ?b_max'"
        unfolding second_price_auction_winner_def second_price_auction_winners_payment_def
        by simp

      have winner_payoff: "payoff (v i) (x ?b i) (p ?b i) = v i - ?b_max'"
        using defined spa is_bid i_range alloc
        by (rule second_price_auction_winner_payoff)

      have non_negative_payoff: "payoff (v i) (x ?b i) (p ?b i) \<ge> 0"
      proof -
        from `?b i \<ge> ?b_max'` have "?b i - ?b_max' \<ge> 0" by simp
        with winner_payoff show ?thesis unfolding b_def by simp
      qed

      show ?thesis
      proof cases -- {* case 1a of the short proof *}
        assume "x whatever_bid i"
        with defined spa alternative_is_bid i_range
        have "payoff (v i) (x whatever_bid i) (p whatever_bid i) = v i - ?b_max'"
          using winners_payoff_on_deviation_from_valuation unfolding b_def by simp
        also have "\<dots> = payoff (v i) (x ?b i) (p ?b i)" using winner_payoff by simp
        finally show ?thesis by (rule eq_refl)
      next -- {* case 1b of the short proof *}
        assume "\<not> x whatever_bid i"
        with spa alternative_is_bid i_range
        have "payoff (v i) (x whatever_bid i) (p whatever_bid i) = 0"
          by (rule second_price_auction_loser_payoff)
        also have "\<dots> \<le> payoff (v i) (x ?b i) (p ?b i)" using non_negative_payoff by simp
        finally show ?thesis .
      qed

    next -- {* case 2 of the short proof *}
      assume non_alloc: "\<not> x ?b i"
      with spa is_bid i_range
      have loser_payoff: "payoff (v i) (x ?b i) (p ?b i) = 0"
        by (rule second_price_auction_loser_payoff)

      have i_bid_at_most_second: "?b i \<le> ?b_max'"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "?b i > ?b_max'" by simp
        with defined spa is_bid i_range
        have "second_price_auction_winner N ?b x p i"
          using only_max_bidder_wins by simp
        with non_alloc show False using second_price_auction_winner_def by simp
      qed

      show ?thesis
      proof cases -- {* case 2a of the short proof *}
        assume "x whatever_bid i"
        with defined spa alternative_is_bid i_range
        have "payoff (v i) (x whatever_bid i) (p whatever_bid i) = ?b i - ?b_max'"
          using winners_payoff_on_deviation_from_valuation unfolding b_def by simp
        also have "\<dots> \<le> 0" using i_bid_at_most_second by simp
        also have "\<dots> = payoff (v i) (x ?b i) (p ?b i)" using loser_payoff by simp
        finally show ?thesis .
      next -- {* case 2b of the short proof *}
        assume "\<not> x whatever_bid i"
        with spa alternative_is_bid i_range
        have "payoff (v i) (x whatever_bid i) (p whatever_bid i) = 0"
          by (rule second_price_auction_loser_payoff)
        also have "\<dots> = payoff (v i) (x ?b i) (p ?b i)" using loser_payoff by simp
        finally show ?thesis by (rule eq_refl)
      qed
    qed
  }
  with spa val bids allocation pay show ?thesis
    unfolding equilibrium_weakly_dominant_strategy_def by simp
qed


subsection {* Part 2: A second-price auction is efficient if all participants bid their valuation. *}

theorem vickreyB:
  fixes N :: participants and v :: "real vector" and x :: allocation and p :: payments
  assumes val: "valuation N v" and spa: "second_price_auction N x p"
  defines "b \<equiv> v"
  shows "efficient N v b x"
proof -
  from val have bids: "bids N v" by (rule valuation_is_bid)
  {
    fix k :: participant
    assume "k \<in> N" and "x b k"
    with spa bids have "k \<in> arg_max_set N v"
      using allocated_implies_spa_winner
      unfolding b_def second_price_auction_winner_def by simp
  }
  with bids show ?thesis using val unfolding b_def efficient_def by blast
qed

end
