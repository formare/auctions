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

lemma skip_index_keeps_non_negativity:
  fixes n::nat and v::"real vector" and i::nat
  assumes non_negative: "non_negative_real_vector n v"
    and range: "i \<in> {1..n}"
  shows "non_negative_real_vector (n - 1) (skip_index v i)"
  unfolding non_negative_real_vector_def
proof
  fix j::nat
  assume j_range: "j \<in> {1..n - 1}"
  have "(skip_index v i) j = (if j < i then v j else v (Suc j))"
    unfolding skip_index_def by auto
  with j_range non_negative show "(skip_index v i) j \<ge> 0"
    unfolding non_negative_real_vector_def by auto
qed

lemma equal_by_skipping:
  fixes n::nat and v::"real vector" and w::"real vector" and j::nat and k::nat
  assumes j_range: "j \<in> {1..n}"
    and equal_except: "\<forall>i \<in> {1..n}. i \<noteq> j \<longrightarrow> v i = w i"
    and k_range: "k \<in> {1..n - 1}"
  shows "skip_index v j k = skip_index w j k"
proof -
  have "skip_index v j k = (if k < j then v k else v (Suc k))"
    and "skip_index w j k = (if k < j then w k else w (Suc k))"
    unfolding skip_index_def by simp_all
  with equal_except k_range show ?thesis by auto
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

lemma deviated_bid_well_formed:
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

lemma allocation_unique:
  fixes n::participants and x::allocation and b::"real vector"
    and winner::participant and other::participant
  assumes "allocation n b x"
    and "winner \<in> {1..n}" and "x b winner"
    and "other \<in> {1..n}" and "x b other"
  shows "other = winner"
  using assms unfolding allocation_def by blast


subsection {* Payment *}

definition vickrey_payment :: "participants \<Rightarrow> real vector \<Rightarrow> payments \<Rightarrow> bool"
  where "vickrey_payment n b p \<longleftrightarrow> bids n b \<and> (\<forall>i \<in> {1..n}. p b i \<ge> 0)"


subsection {* Valuation *}

definition valuation :: "participants \<Rightarrow> real vector \<Rightarrow> bool"
  where "valuation n v \<longleftrightarrow> positive_real_vector n v"

lemma valuation_is_bid:
  fixes n::participants and v::"real vector"
  assumes "valuation n v"
  shows "bids n v"
  using assms
  unfolding valuation_def positive_real_vector_def
  unfolding bids_def non_negative_real_vector_def
  by auto


subsection {* Payoff *}

definition payoff :: "real \<Rightarrow> bool \<Rightarrow> real \<Rightarrow> real"
  where "payoff v x p = v * (if x then 1 else 0) - p"

definition payoff_vector :: "real vector \<Rightarrow> bool vector \<Rightarrow> real vector \<Rightarrow> real vector"
  where "payoff_vector v x p = (\<lambda>i. payoff (v i) (x i) (p i))"


subsection {* Maximum *}

definition maximum :: "nat \<Rightarrow> real vector \<Rightarrow> real"
  where "maximum n y = (if n = 0 then 0 else max 0 (Max (y ` {1..n})))"

lemma maximum_equal:
  fixes n::nat and y::"real vector" and z::"real vector"
  assumes "\<forall>i \<in> {1..n}. y i = z i"
  shows "maximum n y = maximum n z"
proof -
  have "y ` {1..n} = z ` {1..n}" by (rule image_cong) (auto simp add: assms)
  then show ?thesis unfolding maximum_def by simp
qed

lemma maximum_is_greater_or_equal:
  fixes n::nat and y::"real vector" and i::nat
  assumes "i \<in> {1..n}"
  shows "maximum n y \<ge> y i"
proof -
  from assms have "n > 0" and "y i \<le> Max (y ` {1..n})" by simp_all
  then show ?thesis unfolding maximum_def by simp
qed

lemma maximum_Max:
  fixes n::nat and y::"real vector"
  assumes non_empty: "n > 0"
    and non_negative: "non_negative_real_vector n y"
  shows "maximum n y = Max (y ` {1..n})"
proof -
  let ?A = "y ` {1..n}"
  from non_empty have "finite ?A" and "?A \<noteq> {}" by simp_all
  with non_empty non_negative have "0 \<le> Max ?A"
    unfolding non_negative_real_vector_def by (auto simp add: Max_ge_iff)
  with non_empty show ?thesis unfolding maximum_def by simp
qed

lemma maximum_is_component:
  fixes n::nat and y::"real vector"
  assumes non_empty: "n > 0"
    and non_negative: "non_negative_real_vector n y"
  shows "\<exists>i \<in> {1..n}. maximum n y = y i"
proof -
  let ?A = "y ` {1..n}"
  have *: "maximum n y = Max ?A" using non_empty non_negative by (rule maximum_Max)
  from non_empty have "finite ?A" and "?A \<noteq> {}" by simp_all
  then have "Max ?A \<in> ?A" by (rule Max_in)
  then obtain i where "i \<in> {1..n}" and "Max ?A = y i" by auto
  with * show ?thesis by auto
qed

lemma maximum_sufficient:
  fixes n::nat and y::"real vector" and m::real
  assumes non_negative: "non_negative_real_vector n y"
    and non_empty: "n > 0"
    and greater_or_equal: "\<forall>i \<in> {1..n}. m \<ge> y i"
    and is_component: "\<exists>i \<in> {1..n}. m = y i"
  shows "maximum n y = m"
proof -
  let ?A = "y ` {1..n}"
  have "maximum n y = Max ?A" using non_empty non_negative by (rule maximum_Max)
  also have "Max ?A = m"
  proof (rule Max_eqI)
    show "finite ?A" by simp
    show "m \<in> ?A" using is_component by auto
    fix a assume "a \<in> ?A"
    then show "a \<le> m" using greater_or_equal by blast
  qed
  finally show ?thesis .
qed

definition arg_max_set :: "nat \<Rightarrow> real vector \<Rightarrow> nat set"
  where "arg_max_set n b = {i. i \<in> {1..n} \<and> maximum n b = b i}"

definition maximum_except :: "nat \<Rightarrow> real vector \<Rightarrow> nat \<Rightarrow> real"
  where "maximum_except n y j = (if n = 0 then 0 else maximum (n - 1) (skip_index y j))"

lemma maximum_except_is_greater_or_equal:
  fixes n::nat and y::"real vector" and j::nat and i::nat
  assumes j_range: "j \<in> {1..n}"
    and i_range: "i \<in> {1..n}"
    and neq: "i \<noteq> j"
  shows "maximum_except n y j \<ge> y i"
proof -
  let ?y_with_j_skipped = "skip_index y j"
  from j_range have "n > 0" by simp
  from neq have "i < j \<or> i > j" by auto
  then show ?thesis
  proof
    assume "i < j"
    then have can_skip_j: "?y_with_j_skipped i = y i"
      unfolding skip_index_def by simp
    from `i < j` j_range i_range have "i \<in> {1..n - 1}" by simp
    then have "maximum (n - 1) ?y_with_j_skipped \<ge> ?y_with_j_skipped i"
      by (simp add: maximum_is_greater_or_equal)
    with can_skip_j show ?thesis
      by (auto simp add: maximum_def maximum_except_def)
  next
    assume "i > j"
    then have can_skip_j_and_shift_left: "?y_with_j_skipped (i - 1) = y i"
      unfolding skip_index_def by (cases i) simp_all
    from `i > j` i_range j_range have "i - 1 \<in> {1..n - 1}"
      by (cases i) simp_all
    then have "maximum (n - 1) ?y_with_j_skipped \<ge> ?y_with_j_skipped (i - 1)"
      by (simp add: maximum_is_greater_or_equal)
    with can_skip_j_and_shift_left show ?thesis
      by (auto simp add: maximum_def maximum_except_def)
  qed
qed

lemma maximum_greater_or_equal_remaining_maximum:
  fixes n::nat and y::"real vector" and j::nat
  assumes non_negative: "non_negative_real_vector n y"
    and non_trivial: "n > 1"
    and range: "j \<in> {1..n}"
  shows "y j \<ge> maximum_except n y j \<longleftrightarrow> maximum n y = y j"
proof
  assume ge_remaining: "y j \<ge> maximum_except n y j"
  from non_trivial range
  have "\<forall>i \<in> {1..n}. i \<noteq> j \<longrightarrow> maximum_except n y j \<ge> y i"
    by (simp add: maximum_except_is_greater_or_equal)
  with ge_remaining have "\<forall>i \<in> {1..n}. i \<noteq> j \<longrightarrow> y j \<ge> y i" by auto
  then have greater_or_equal: "\<forall>i \<in> {1..n}. y j \<ge> y i" by auto
  from range have is_component: "\<exists>i \<in> {1..n}. y j = y i" by auto
  with non_negative non_trivial greater_or_equal show "maximum n y = y j"
    by (simp add: maximum_sufficient)
next
  assume j_max: "maximum n y = y j"
  from non_trivial
  have maximum_except_unfolded: "maximum_except n y j = maximum (n - 1) (skip_index y j)"
    by (simp add: maximum_except_def)
  show "y j \<ge> maximum_except n y j"
  proof -
    from j_max [symmetric] have ge: "\<forall>k \<in> {1..n}. y j \<ge> y k"
      by (simp add: maximum_is_greater_or_equal)
    from non_negative range
    have pred_non_negative: "non_negative_real_vector (n - 1) (skip_index y j)"
      by (rule skip_index_keeps_non_negativity)
    from non_trivial have "n - 1 > 0" by simp
    with pred_non_negative maximum_is_component
    obtain i where i_range: "i \<in> {1..n - 1}" and
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
  with non_empty show ?thesis by (simp add: maximum_except_def)
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

definition second_price_auction_loser ::
    "participants \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where "second_price_auction_loser n b x p i \<longleftrightarrow> i \<in> {1..n} \<and> \<not> x b i \<and> p b i = 0"

definition second_price_auction :: "participants \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where
    "second_price_auction n x p \<longleftrightarrow>
      (\<forall>b. bids n b \<longrightarrow> allocation n b x \<and> vickrey_payment n b p \<and>
        (\<exists>i \<in> {1..n}. second_price_auction_winner n b x p i \<and>
          (\<forall>j \<in> {1..n}. j \<noteq> i \<longrightarrow> second_price_auction_loser n b x p j)))"

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

lemma second_price_auction_winner_payoff:
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
    "efficient n v b x \<longleftrightarrow>
      valuation n v \<and> bids n b \<and> (\<forall>i \<in> {1..n}. x b i \<longrightarrow> i \<in> arg_max_set n v)"


subsection {* Equilibrium in weakly dominant strategies *}

definition equilibrium_weakly_dominant_strategy ::
  "participants \<Rightarrow> real vector \<Rightarrow> real vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool" where
  "equilibrium_weakly_dominant_strategy n v b x p \<longleftrightarrow>
    valuation n v \<and> bids n b \<and> allocation n b x \<and> vickrey_payment n b p \<and>
    (\<forall>i \<in> {1..n}.
      (\<forall>whatever_bid. bids n whatever_bid \<and> whatever_bid i \<noteq> b i \<longrightarrow>
        (let i_sticks_with_bid = whatever_bid(i := b i)
         in payoff_vector v (x i_sticks_with_bid) (p i_sticks_with_bid) i \<ge>
            payoff_vector v (x whatever_bid) (p whatever_bid) i)))"


section {* Vickrey's Theorem *}

subsection {* Part 1: A second-price auction supports an equilibrium in weakly dominant
  strategies if all participants bid their valuation. *}

theorem vickreyA:
  fixes n :: participants and v :: "real vector" and x :: allocation and p :: payments
  assumes non_trivial: "n > 1"
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

    fix whatever_bid :: "real vector"
    assume alternative_is_bid: "bids n whatever_bid"

    let ?i_sticks_with_strategy = "whatever_bid(i := ?b i)"
    from bids alternative_is_bid
    have i_sticks_is_bid: "bids n ?i_sticks_with_strategy"
      by (simp add: deviated_bid_well_formed)

    txt {* Agent @{term i} sticks to his/her strategy (i.e. truthful bidding), whatever the others bid.
      Given this, we have to show that agent @{term i} is best off. *}

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
          using i_sticks_is_bid bids_def non_trivial i_range
          maximum_greater_or_equal_remaining_maximum
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
          with spa alternative_is_bid non_trivial i_range
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
          with spa alternative_is_bid non_trivial i_range
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
