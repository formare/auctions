theory Cramton
imports Vickrey

begin

section{* Cramton's Applicant Auctions (simplified variant of simultaneous ascending clock auction) *}
definition cramton_auction_winner :: "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where "cramton_auction_winner n b x p i \<equiv> second_price_auction_winner n b x p i"

definition cramton_auction_loser :: "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool"
  where "cramton_auction_loser n b x p i \<equiv> i \<in> {1..n} \<and> \<not>x b i \<and> (p b i = -(maximum_except n b i) / (n - 1))"

definition cramton_auction :: "participants \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool"
  where "cramton_auction n x p \<equiv>
    \<forall>b::real_vector . bids n b \<longrightarrow> allocation n b x \<and> vickrey_payment n b p \<and>
    (\<exists>i::participant. i \<in> {1..n} \<and> cramton_auction_winner n b x p i
                      \<and> (\<forall>j::participant. j \<in> {1..n} \<and> j \<noteq> i \<longrightarrow> cramton_auction_loser n b x p j))"

text{* strategy of a single participant *}
definition cramton_strategy :: "participants \<Rightarrow> real \<Rightarrow> real"
  where "cramton_strategy n v \<equiv> v * (n - 1) / n"

text{* vector of strategies of all participants *}
definition cramton_strategy_vector :: "participants \<Rightarrow> real_vector \<Rightarrow> real_vector"
  where "cramton_strategy_vector n v i \<equiv> cramton_strategy n (v i)"

lemma cramton_strategy_is_bid :
  fixes n::participants and v::real_vector
  assumes val: "valuation n v"
      and more_than_one: "n > 1"
  shows "bids n (cramton_strategy_vector n v)"
proof -
  {
    fix i::participant
    assume "i \<in> {1..n}"
    with val have positive: "v i > 0" unfolding valuation_def positive_real_vector_def by simp
    with more_than_one have "cramton_strategy_vector n v i > 0" unfolding cramton_strategy_vector_def cramton_strategy_def
      by (metis divide_pos_pos gr_implies_not0 linorder_antisym_conv2 mult_pos_pos natfloor_real_of_nat natfloor_zero real_of_nat_ge_zero zero_less_diff)
    then have "cramton_strategy_vector n v i \<ge> 0" by arith
  }
  then show ?thesis unfolding bids_def non_negative_real_vector_def by simp
qed

theorem cramton_weakly_dominant_strategy :
  fixes n::participants and v::real_vector and x::allocation and p::payments
  assumes val: "valuation n v" and ca: "cramton_auction n x p"
  shows "equilibrium_weakly_dominant_strategy n v (cramton_strategy_vector n v) x p"
proof -
  let ?b = "cramton_strategy_vector n v" (* the bids according to the strategy we want to prove optimal *)
  from val have bids: "bids n ?b" sorry
oops

