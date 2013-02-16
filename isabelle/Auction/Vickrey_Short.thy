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


section {* Vectors *}

type_synonym 'a vector = "nat \<Rightarrow> 'a"

definition non_negative_real_vector :: "nat \<Rightarrow> real vector \<Rightarrow> bool"
  where "non_negative_real_vector n v \<longleftrightarrow> (\<forall>i \<in> {1..n}. v i \<ge> 0)"

definition positive_real_vector :: "nat \<Rightarrow> real vector \<Rightarrow> bool"
  where "positive_real_vector n v \<longleftrightarrow> (\<forall>i \<in> {1..n}. v i > 0)"


definition skip_index :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a vector"
  where "skip_index vector index = (\<lambda>i. vector (if i < index then i else Suc i))"

lemma skip_index_keeps_non_negativity :
  fixes n::nat and v::"real vector" and i::nat
  assumes non_negative: "non_negative_real_vector n v"
    and range: "i \<in> {1..n}"
  shows "non_negative_real_vector (n - 1) (skip_index v i)"
proof -
  {
    fix j::nat
    assume j_range: "j \<in> {1..n - 1}"
    have "(skip_index v i) j \<ge> 0"
    proof (cases "j < i")
      case True
      then have "(skip_index v i) j = v j" unfolding skip_index_def by simp
      with j_range non_negative show ?thesis
        unfolding non_negative_real_vector_def
        by (auto simp add: leD less_imp_diff_less not_leE)
    next
      case False
      then have "(skip_index v i) j = v (Suc j)" unfolding skip_index_def by simp
      with j_range non_negative show ?thesis
        unfolding non_negative_real_vector_def
        by (auto simp add: leD less_imp_diff_less not_leE)
    qed
  }
  then show "non_negative_real_vector (n - 1) (skip_index v i)"
    unfolding non_negative_real_vector_def by simp
qed

lemma equal_by_skipping :
  fixes n::nat and v::"real vector" and w::"real vector" and j::nat and k::nat
  assumes j_range: "j \<in> {1..n}"
    and equal_except: "\<forall>i \<in> {1..n}. i \<noteq> j \<longrightarrow> v i = w i"
    and k_range: "k \<in> {1..n - 1}"
  shows "skip_index v j k = skip_index w j k"
proof (cases "k < j")
  case True
  then have "skip_index v j k = v k" and "skip_index w j k = w k"
    unfolding skip_index_def by auto
  with equal_except k_range True show ?thesis by auto
next
  case False
  then have "skip_index v j k = v (Suc k)" and "skip_index w j k = w (Suc k)"
    unfolding skip_index_def by auto
  with equal_except k_range False show ?thesis by auto
qed



section {* Single good auctions *}

subsection {* Preliminaries *}

type_synonym participant = "nat"  (* ordinal number *)
type_synonym participants = "nat" (* cardinal number *)

type_synonym allocation = "real vector \<Rightarrow> participants \<Rightarrow> bool"
type_synonym payments = "real vector \<Rightarrow> participants \<Rightarrow> real"


subsection {* Strategy (bids) *}

definition bids :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "bids n b \<longleftrightarrow> non_negative_real_vector n b"


subsubsection {* Deviation from a bid *}

lemma deviated_bid_well_formed :
  fixes n::participants and bid::"real vector"
    and alternative_vec::"real vector" and i::participant
  assumes "bids n bid" and "bids n alternative_vec"
  shows "bids n (bid(i := alternative_vec i))"  (is "bids _ ?dev")
proof -
  {
    fix k::participant
    assume "k \<in> {1..n}"
    with assms have "?dev k \<ge> 0" by (simp add: bids_def non_negative_real_vector_def)
  }
  then show "bids n ?dev" by (simp add: bids_def non_negative_real_vector_def)
qed


subsection {* Allocation *}

definition allocation :: "participants \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> bool"
  where "allocation n b x \<longleftrightarrow> bids n b \<and> (\<exists>!i \<in> {1..n}. x b i)"

lemma allocation_unique :
  fixes n::participants and x::allocation and b::"real vector" and winner::participant and other::participant
  assumes "allocation n b x"
    and "winner \<in> {1..n}" and "x b winner"
    and "other \<in> {1..n}" and "x b other"
  shows "other = winner"
  using assms unfolding allocation_def by blast


subsection {* Payment *}

definition vickrey_payment :: "participants \<Rightarrow> real vector \<Rightarrow> payments \<Rightarrow> bool"
  where "vickrey_payment n b p \<longleftrightarrow> bids n b \<and> (\<forall>i::participant \<in> {1..n}. p b i \<ge> 0)"


subsection {* Valuation *}

definition valuation :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "valuation n v \<longleftrightarrow> positive_real_vector n v"

lemma valuation_is_bid :
  fixes n::participants and v::"real vector"
  assumes "valuation n v"
  shows "bids n v"
  using assms
  unfolding valuation_def positive_real_vector_def
  unfolding bids_def non_negative_real_vector_def
  by (simp add: order_less_imp_le)


subsection {* Payoff *}

definition payoff :: "real \<Rightarrow> bool \<Rightarrow> real \<Rightarrow> real"
  where
    "payoff Valuation Allocation Payment =
      Valuation * (if Allocation then 1 else 0) - Payment"

definition payoff_vector :: "real vector \<Rightarrow> bool vector \<Rightarrow> real vector \<Rightarrow> participant \<Rightarrow> real"
  where "payoff_vector v concrete_x concrete_p i = payoff (v i) (concrete_x i) (concrete_p i)"


subsection {* Maximum *}

fun maximum :: "nat \<Rightarrow> real vector \<Rightarrow> real"
where
  "maximum 0 _ = 0"
| "maximum (Suc n) y = max 0 (max (maximum n y) (y (Suc n)))"

lemma maximum_equal:
  fixes n::nat and y::"real vector" and z::"real vector"
  assumes "\<forall>i \<in> {1..n}. y i = z i"
  shows "maximum n y = maximum n z"
  using assms by (induct n) simp_all

lemma maximum_non_negative:
  fixes n::nat and y::"real vector"
  shows "maximum n y \<ge> 0"
  by (induct n) simp_all

lemma maximum_is_greater_or_equal:
  fixes n::nat and y::"real vector" and i::nat
  assumes "i \<in> {1..n}"
  shows "maximum n y \<ge> y i"
  using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "max (maximum n y) (y (Suc n)) \<ge> y i"
  proof (cases "i = Suc n")
    case True
    then show ?thesis by (simp add: le_max_iff_disj)
  next
    case False
    with Suc.prems
      have "i \<in> {1..n}" by (simp add: less_eq_Suc_le)
    then have "maximum n y \<ge> y i" by (simp add: Suc.hyps)
    then show ?thesis by (simp add: le_max_iff_disj)
  qed
  then show "maximum (Suc n) y \<ge> y i" using maximum_def by simp
qed

lemma maximum_is_component:
  fixes n::nat and y::"real vector"
  assumes "n > 0 \<and> non_negative_real_vector n y"
  shows "\<exists>i \<in> {1..n}. maximum n y = y i"
  using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show "\<exists>i \<in> {1..Suc n}. maximum (Suc n) y = y i"
  proof (cases "y (Suc n) \<ge> maximum n y")
    case True
    from Suc.prems have "y (Suc n) \<ge> 0"
      unfolding non_negative_real_vector_def by simp
    with True have "y (Suc n) = maximum (Suc n) y" using maximum_def by simp
    then show ?thesis by auto
  next
    case False
    have non_empty: "n > 0"
    proof - (* by contradiction *)
      {
        assume "n = 0"
        with False Suc.prems have "y (Suc n) = maximum n y"
          using non_negative_real_vector_def maximum_def
          by auto
        with False have "False" by simp
      }
      then show "n > 0" by blast
    qed
    from Suc.prems have pred_non_negative: "non_negative_real_vector n y"
      unfolding non_negative_real_vector_def
      by simp
    with non_empty obtain i::nat where "i \<in> {1..n}" and pred_max: "maximum n y = y i"
      by (metis Suc.hyps)
    with Suc.prems have y_i_non_negative: "0 \<le> y i"
      unfolding non_negative_real_vector_def by simp
    have "y i = maximum n y" by (rule pred_max [symmetric])
    also have "\<dots> = max (maximum n y) (y (Suc n))" using False by simp
    also have "\<dots> = max 0 (max (maximum n y) (y (Suc n)))"
      using Suc.prems y_i_non_negative by (auto simp add: calculation min_max.le_iff_sup)
    also have "\<dots> = maximum (Suc n) y" using maximum_def non_empty by simp
    finally have "y i = maximum (Suc n) y" .
    from `i \<in> {1..n}` and this [symmetric] show ?thesis by auto
  qed
qed

lemma maximum_sufficient:
  fixes n::nat and y::"real vector" and m::real
  assumes non_negative: "non_negative_real_vector n y"
    and non_empty: "n > 0"
    and greater_or_equal: "\<forall>i \<in> {1..n}. m \<ge> y i"
    and is_component: "\<exists>i \<in> {1..n}. m = y i"
  shows "m = maximum n y"
  using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems(1) have pred_non_negative: "non_negative_real_vector n y"
    unfolding non_negative_real_vector_def by simp
  from non_empty have max_def: "maximum (Suc n) y =
    max 0 (max (maximum n y) (y (Suc n)))" using maximum_def by simp
  also have "\<dots> = m"
  proof (cases "n = 0")
    case True
    with Suc.prems(4) have m_is_only_component: "m = y 1" by simp
    with Suc.prems(1) have "m \<ge> 0" unfolding non_negative_real_vector_def by simp
    then have "max 0 (max (maximum 0 y) (y 1)) = m"
      by (auto simp add: m_is_only_component)
    with True show ?thesis by simp
  next
    case False
    show ?thesis
    proof cases
      assume last_is_max: "y (Suc n) = m"
      have "\<dots> \<ge> maximum n y"
      proof -
        from False pred_non_negative maximum_is_component
        obtain k::nat where "k \<in> {1..n}" and "maximum n y = y k" by blast
        with Suc.prems(3) show ?thesis by simp
      qed
      then show ?thesis
        using last_is_max
        by (metis less_max_iff_disj linorder_not_le
            maximum_non_negative min_max.sup_absorb1 min_max.sup_commute)
    next
      assume last_is_not_max: "y (Suc n) \<noteq> m"
      from Suc.prems(4) obtain i where "i \<in> {1..Suc n}" and "m = y i" by auto
      with last_is_not_max atLeastAtMostSuc_conv have "i \<in> {1..n}" by auto
      from this and `m = y i` have pred_is_component: "\<exists>k \<in> {1..n}. m = y k" ..
      from Suc.prems(3) have "\<forall>k \<in> {1..n}. m \<ge> y k" by simp
      then have "m = maximum n y"
        using pred_is_component pred_non_negative by (metis False Suc.hyps gr0I)
      then show ?thesis using Suc.prems(3) maximum_non_negative
        by (metis Suc(2) Suc.prems(4) maximum.simps(2)
            maximum_is_component maximum_is_greater_or_equal
            min_max.le_iff_sup min_max.sup_absorb1 zero_less_Suc)
    qed
  qed
  finally show "m = maximum (Suc n) y" ..
qed

definition arg_max_set :: "nat \<Rightarrow> real vector \<Rightarrow> (nat set)"
  where "arg_max_set n b = {i. i \<in> {1..n} \<and> maximum n b = b i}"

fun maximum_except :: "nat \<Rightarrow> real vector \<Rightarrow> nat \<Rightarrow> real"
where
  "maximum_except 0 _ _ = 0"
| "maximum_except (Suc n) y j = maximum n (skip_index y j)"

lemma maximum_except_is_greater_or_equal:
  fixes n::nat and y::"real vector" and j::nat and i::nat
  assumes j_range: "n \<ge> 1 \<and> j \<in> {1..n}"
    and i_range: "i \<in> {1..n} \<and> i \<noteq> j"
  shows "maximum_except n y j \<ge> y i"
proof -
  let ?y_with_j_skipped = "skip_index y j"
  from j_range obtain pred_n where pred_n: "n = Suc pred_n"
    by (metis not0_implies_Suc not_one_le_zero)
  then show "maximum_except n y j \<ge> y i"
  proof (cases "i < j")
    case True
    then have can_skip_j: "y i = ?y_with_j_skipped i" unfolding skip_index_def by simp
    from True j_range i_range pred_n have "i \<in> {1..pred_n}" by simp
    then have "maximum pred_n ?y_with_j_skipped \<ge> ?y_with_j_skipped i"
      by (simp add: maximum_is_greater_or_equal)
    with can_skip_j pred_n show ?thesis by simp
  next
    case False
    with i_range have case_False_nice: "i > j" by simp
    then obtain pred_i where pred_i: "i = Suc pred_i" by (rule lessE)
    from case_False_nice pred_i have can_skip_j_and_shift_left: "y i = ?y_with_j_skipped pred_i"
      unfolding skip_index_def by simp
    from case_False_nice i_range j_range pred_i pred_n
    have "pred_i \<in> {1..pred_n}" by simp
    then have "maximum pred_n ?y_with_j_skipped \<ge> ?y_with_j_skipped pred_i"
      by (simp add: maximum_is_greater_or_equal)
    with can_skip_j_and_shift_left pred_n show ?thesis by simp
  qed
qed

lemma maximum_greater_or_equal_remaining_maximum:
  fixes n::nat and y::"real vector" and j::nat
  assumes non_negative: "non_negative_real_vector n y"
    and non_empty: "n > 0"
    and range: "j \<in> {1..n}"
  shows "y j \<ge> maximum_except n y j \<longleftrightarrow> y j = maximum n y"
proof
  assume ge_remaining: "y j \<ge> maximum_except n y j"
  from non_empty range
  have "\<forall>i \<in> {1..n}. i \<noteq> j \<longrightarrow> maximum_except n y j \<ge> y i"
    by (simp add: maximum_except_is_greater_or_equal)
  with ge_remaining have "\<forall>i \<in> {1..n}. i \<noteq> j \<longrightarrow> y j \<ge> y i" by auto
  then have greater_or_equal: "\<forall>i \<in> {1..n}. y j \<ge> y i" by auto
  from range have is_component: "\<exists>i \<in> {1..n}. y j = y i" by auto
  with non_negative non_empty greater_or_equal show "y j = maximum n y"
    by (simp add: maximum_sufficient)
next
  assume j_max: "y j = maximum n y"
  from non_empty
  have maximum_except_unfolded: "maximum_except n y j = maximum (n - 1) (skip_index y j)"
    by (metis Suc_diff_1 maximum_except.simps(2))
  show "y j \<ge> maximum_except n y j"
  proof (cases "n = 1")
    case True
    with maximum_except_unfolded maximum_def have "maximum_except n y j = 0" by simp
    with j_max non_negative show ?thesis by (simp add: maximum_non_negative)
  next
    case False
    from j_max have ge: "\<forall>k \<in> {1..n}. y j \<ge> y k" by (simp add: maximum_is_greater_or_equal)
    from False non_empty have "n > 1" by simp
    then have pred_non_empty: "n - 1 > 0" by simp
    from non_empty non_negative range
    have pred_non_negative: "non_negative_real_vector (n - 1) (skip_index y j)"
      by (metis skip_index_keeps_non_negativity)
    from pred_non_empty pred_non_negative maximum_is_component
    obtain i::nat where i_range: "i \<in> {1..n - 1}" and
      maximum_except_component: "maximum (n - 1) (skip_index y j) = (skip_index y j) i"
      by blast
    from maximum_except_component maximum_except_unfolded
    have maximum_except_component_nice: "maximum_except n y j = (skip_index y j) i"
      by simp
    have skip_index_range: "\<dots> = y i \<or> (skip_index y j) i = y (Suc i)"
      unfolding skip_index_def by simp
    from i_range have 1: "i \<in> {1..n}" by auto
    from i_range have 2: "Suc i \<in> {1..n}" by auto
    from skip_index_range 1 2 have "\<exists>k \<in> {1..n}. (skip_index y j) i = y k" by auto
    with ge maximum_except_component_nice show "y j \<ge> maximum_except n y j" by auto
  qed
qed

lemma remaining_maximum_invariant:
  fixes n::nat and y::"real vector" and i::nat and a::real
  assumes non_empty: "n > 0"
    and range: "i \<in> {1..n}"
  shows "maximum_except n y i = maximum_except n (y(i := a)) i"
proof -
  from range have equal_except: "\<forall>j \<in> {1..n}. j \<noteq> i \<longrightarrow> y j = (y(i := a)) j" by simp
  with non_empty range have "\<forall>k \<in> {1..n - 1}. skip_index y i k = skip_index (y(i := a)) i k"
    using equal_by_skipping by auto
  then have "maximum (n - 1) (skip_index y i) =
    maximum (n - 1) (skip_index (y(i := a)) i)" by (simp add: maximum_equal)
  with non_empty show ?thesis by (metis Suc_pred' maximum_except.simps(2))
qed


subsection {* Second price single good auctions and some of their properties *}

definition second_price_auction_winners_payment ::
    "participants \<Rightarrow> real vector \<Rightarrow> participant \<Rightarrow> real"
  where "second_price_auction_winners_payment n b winner = maximum_except n b winner"

definition second_price_auction_winner ::
    "participants \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where
    "second_price_auction_winner n b x p i \<longleftrightarrow>
      i \<in> {1..n} \<and> i \<in> arg_max_set n b \<and> x b i \<and>
      (p b i = second_price_auction_winners_payment n b i)"

definition second_price_auction_loser :: "participants \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where "second_price_auction_loser n b x p i \<longleftrightarrow> i \<in> {1..n} \<and> \<not> x b i \<and> p b i = 0"

definition second_price_auction :: "participants \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "second_price_auction n x p \<longleftrightarrow>
      (\<forall>b::real vector. bids n b \<longrightarrow> allocation n b x \<and> vickrey_payment n b p \<and>
        (\<exists>i::participant \<in> {1..n}. second_price_auction_winner n b x p i \<and>
          (\<forall>j::participant \<in> {1..n}. j \<noteq> i \<longrightarrow> second_price_auction_loser n b x p j)))"

lemma allocated_implies_spa_winner:
  fixes n::participants and x::allocation and p::payments
    and b::"real vector" and winner::participant
  assumes "second_price_auction n x p"
    and "bids n b"
    and "winner \<in> {1..n}"
    and "x b winner"
  shows "second_price_auction_winner n b x p winner"
  using assms
  unfolding second_price_auction_def second_price_auction_winner_def
  using allocation_unique
  by blast

lemma not_allocated_implies_spa_loser:
  fixes n::participants and x::allocation and p::payments
    and b::"real vector" and loser::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "loser \<in> {1..n}"
    and loses: "\<not> x b loser"
  shows "second_price_auction_loser n b x p loser"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "x b loser"
    using spa bids
    using range
    unfolding second_price_auction_def second_price_auction_winner_def
    by force
  with loses show "False" by contradiction
qed

lemma only_max_bidder_wins:
  fixes n::participants and max_bidder::participant
    and b::"real vector" and x::allocation and p::payments
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "max_bidder \<in> {1..n}"
    and only_max_bidder: "b max_bidder > maximum_except n b max_bidder"
  shows "second_price_auction_winner n b x p max_bidder"
proof -
  from bids spa
  have spa_unfolded: "\<exists>i. second_price_auction_winner n b x p i \<and>
      (\<forall>j \<in> {1..n}. j \<noteq> i \<longrightarrow> second_price_auction_loser n b x p j)"
    unfolding second_price_auction_def by blast
  then have x_is_allocation: "\<exists>i \<in> {1..n}. x b i \<and> (\<forall>j \<in> {1..n}. j\<noteq>i \<longrightarrow> \<not> x b j)"
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
      qed
    qed
  }
  with x_is_allocation spa_unfolded
    show ?thesis by (auto simp add: second_price_auction_winner_def)
qed

lemma second_price_auction_winner_payoff :
  fixes n::participants and v::"real vector" and x::allocation
    and b::"real vector" and p::payments and winner::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and winner_range: "winner \<in> {1..n}"
    and wins: "x b winner"
  shows "payoff_vector v (x b) (p b) winner = v winner - maximum_except n b winner"
proof -
  have "payoff_vector v (x b) (p b) winner =
      payoff (v winner) (x b winner) (p b winner)"
    unfolding payoff_vector_def by simp
  also have "\<dots> = payoff (v winner) True (p b winner)" using wins by simp
  also have "\<dots> = v winner - p b winner" unfolding payoff_def by simp
  also have "\<dots> = v winner - maximum_except n b winner"
    using spa bids winner_range wins
    using allocated_implies_spa_winner
    unfolding second_price_auction_winner_def second_price_auction_winners_payment_def
    by simp
  finally show ?thesis .
qed

lemma second_price_auction_loser_payoff:
  fixes n::participants and v::"real vector" and x::allocation
    and b::"real vector" and p::payments and loser::participant
  assumes "second_price_auction n x p"
    and "bids n b"
    and "loser \<in> {1..n}"
    and "\<not> x b loser"
  shows "payoff_vector v (x b) (p b) loser = 0"
  using assms not_allocated_implies_spa_loser
  unfolding second_price_auction_loser_def payoff_vector_def payoff_def by simp

lemma winners_payoff_on_deviation_from_valuation:
  fixes n::participants and v::"real vector" and x::allocation
    and b::"real vector" and p::payments and winner::participant
  assumes non_empty: "n > 0"
    and spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "winner \<in> {1..n}"
    and wins: "x b winner"
  shows
    "let winner_sticks_with_valuation = b(winner := v winner)
    in payoff_vector v (x b) (p b) winner =
      v winner - maximum_except n winner_sticks_with_valuation winner"
  using wins range spa bids second_price_auction_winner_payoff
  using non_empty remaining_maximum_invariant
  by simp


section {* Some properties that single good auctions can have *}

subsection {* Efficiency *}

definition efficient :: "participants \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> bool"
  where
    "efficient n v b x \<longleftrightarrow> valuation n v \<and> bids n b \<and>
      (\<forall>i::participant \<in> {1..n}. x b i \<longrightarrow> i \<in> arg_max_set n v)"


subsection {* Equilibrium in weakly dominant strategies *}

definition equilibrium_weakly_dominant_strategy ::
  "participants \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool" where
  "equilibrium_weakly_dominant_strategy n v b x p \<longleftrightarrow>
    valuation n v \<and> bids n b \<and> allocation n b x \<and> vickrey_payment n b p \<and>
   (\<forall>i::participant \<in> {1..n}.
     (\<forall>whatever_bid::real vector. bids n whatever_bid \<and> whatever_bid i \<noteq> b i \<longrightarrow> (
       let i_sticks_with_bid = whatever_bid(i := b i)
       in payoff_vector v (x i_sticks_with_bid) (p i_sticks_with_bid) i \<ge>
          payoff_vector v (x whatever_bid) (p whatever_bid) i)))"


section {* Vickrey's Theorem *}

subsection {* Part 1: A second-price auction supports an equilibrium in weakly dominant
  strategies if all participants bid their valuation. *}

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
    assume alternative_is_bid: "bids n whatever_bid"
    let ?i_sticks_with_strategy = "whatever_bid(i := ?b i)"
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
        txt {* @{term i} gets the good, so @{term i} also satisfies the further properties of a
          second price auction winner: *}
        with spa i_sticks_is_bid i_range
        have "i \<in> arg_max_set n ?i_sticks_with_strategy"
          using allocated_implies_spa_winner by (simp add: second_price_auction_winner_def)
        then have "?i_sticks_with_strategy i = maximum n ?i_sticks_with_strategy"
          by (simp add: arg_max_set_def)
        also have "\<dots> \<ge> maximum_except n ?i_sticks_with_strategy i"
          using i_sticks_is_bid bids_def non_empty i_range
          by (metis calculation maximum_greater_or_equal_remaining_maximum)
        finally
        have i_ge_max_except:
            "?i_sticks_with_strategy i \<ge> maximum_except n ?i_sticks_with_strategy i" .
        txt {* Now we show that @{term i}'s payoff is @{text "\<ge> 0"}. *}
        from spa i_sticks_is_bid i_range i_wins
        have winners_payoff:
          "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i =
            v i - maximum_except n ?i_sticks_with_strategy i"
          by (simp add: second_price_auction_winner_payoff)
        also have "\<dots> = ?i_sticks_with_strategy i - maximum_except n ?i_sticks_with_strategy i"
          by simp
        finally have payoff_expanded:
          "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i =
            ?i_sticks_with_strategy i - maximum_except n ?i_sticks_with_strategy i" .
        also have "\<dots> \<ge> 0" using i_ge_max_except by simp
        finally
        have non_negative_payoff:
            "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i \<ge> 0" .
        show ?thesis
        proof cases -- {* case 1a of the short proof *}
          assume "x whatever_bid i"
          with spa alternative_is_bid non_empty i_range
          have "payoff_vector v (x whatever_bid) (p whatever_bid) i =
              v i - maximum_except n ?i_sticks_with_strategy i"
            using winners_payoff_on_deviation_from_valuation by simp
          txt {* Now we show that @{term i}'s payoff hasn't changed. *}
          also have "\<dots> =
              payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i"
            using winners_payoff by simp
          finally show ?thesis by (rule eq_refl)
        next -- {* case 1b of the short proof *}
          assume "\<not> x whatever_bid i"
          with spa alternative_is_bid i_range
          have "payoff_vector v (x whatever_bid) (p whatever_bid) i = 0"
            by (rule second_price_auction_loser_payoff)
          also have "\<dots> \<le>
              payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i"
            using non_negative_payoff by simp
          finally show ?thesis .
        qed
      next -- {* case 2 of the short proof *}
        assume i_loses: "\<not> x ?i_sticks_with_strategy i"
        txt {* @{term i} doesn't get the good, so @{term i}'s payoff is @{text 0} *}
        with spa i_sticks_is_bid i_range
        have zero_payoff:
          "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i = 0"
          by (rule second_price_auction_loser_payoff)
        txt {* @{term i}'s bid can't be higher than the second highest bid, as otherwise
          @{term i} would have won *}
        have i_bid_at_most_second:
          "?i_sticks_with_strategy i \<le> maximum_except n ?i_sticks_with_strategy i"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then have "?i_sticks_with_strategy i >
            maximum_except n ?i_sticks_with_strategy i" by simp
          with spa i_sticks_is_bid i_range
          have "second_price_auction_winner n ?i_sticks_with_strategy x p i"
            using only_max_bidder_wins
            by simp
          with i_loses show False using second_price_auction_winner_def by simp
        qed
        show ?thesis
        proof cases -- {* case 2a of the short proof *}
          assume "x whatever_bid i"
          with spa alternative_is_bid non_empty i_range
          have "payoff_vector v (x whatever_bid) (p whatever_bid) i =
              ?i_sticks_with_strategy i - maximum_except n ?i_sticks_with_strategy i"
            using winners_payoff_on_deviation_from_valuation by simp
          txt {* Now we can compute @{term i}'s payoff *}
          also have "\<dots> \<le> 0" using i_bid_at_most_second by simp
          also have "\<dots> =
              payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i"
            using zero_payoff by simp
          finally show ?thesis .
        next -- {* case 2b of the short proof *}
          assume "\<not> x whatever_bid i"
          txt {* @{term i} doesn't get the good, so @{term i}'s payoff is @{text 0} *}
          with spa alternative_is_bid i_range
          have "payoff_vector v (x whatever_bid) (p whatever_bid) i = 0"
            by (rule second_price_auction_loser_payoff)
          also have "\<dots> =
              payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i"
            using zero_payoff by simp
          finally show ?thesis by (rule eq_refl)
        qed
      qed
    qed
  }
  with spa val bids alloc pay show ?thesis
    unfolding equilibrium_weakly_dominant_strategy_def by simp
qed


subsection {* Part 2: A second-price auction is efficient if all participants bid their valuation. *}

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

end
