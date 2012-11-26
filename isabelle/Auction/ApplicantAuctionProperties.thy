theory ApplicantAuctionProperties
imports ApplicantAuction

begin

text{* best (?) strategy of a single participant *}
definition applicant_strategy :: "participants \<Rightarrow> real \<Rightarrow> real"
  where "applicant_strategy n v \<equiv> v * (n - 1) / n"

lemma applicant_strategy_lt_valuation :
  fixes n::participants and v::real
  assumes val: "v > 0"
      and more_than_one: "n > 1"
  shows "applicant_strategy n v < v"
proof -
  from more_than_one have "(n - 1) / n < 1"
    by (metis add_diff_inverse diff_add_inverse2 diff_le_self diff_self_eq_0 divide_less_eq
              mult_1 nat_less_le not_real_of_nat_less_zero order_less_asym real_of_nat_less_iff zero_less_one)
  (* Doing both steps at once doesn't work; "by arith" doesn't work either. *)
  with val show ?thesis unfolding applicant_strategy_def by (metis mult.comm_neutral mult_strict_left_mono times_divide_eq_right)
qed

text{* vector of strategies of all participants *}
definition applicant_strategy_vector :: "participants \<Rightarrow> real_vector \<Rightarrow> real_vector"
  where "applicant_strategy_vector n v i \<equiv> applicant_strategy n (v i)"

lemma applicant_strategy_is_bid :
  fixes n::participants and v::real_vector
  assumes val: "valuation n v"
      and more_than_one: "n > 1"
  shows "bids n (applicant_strategy_vector n v)"
proof -
  {
    fix i::participant
    assume "i \<in> {1..n}"
    with val have positive: "v i > 0" unfolding valuation_def positive_real_vector_def by simp
    with more_than_one have "applicant_strategy_vector n v i > 0" unfolding applicant_strategy_vector_def applicant_strategy_def
      by (metis divide_pos_pos gr_implies_not0 linorder_antisym_conv2 mult_pos_pos natfloor_real_of_nat natfloor_zero real_of_nat_ge_zero zero_less_diff)
    then have "applicant_strategy_vector n v i \<ge> 0" by simp
  }
  then show ?thesis unfolding bids_def non_negative_real_vector_def by simp
qed

text{* This is analogous to Vickrey's theorem part A, but for our variant of applicant auctions, and the strategy for them. *}
theorem applicant_strategy_weakly_dominant :
  fixes n::participants and v::real_vector and x::allocation and p::payments
  assumes val: "valuation n v" and aa: "applicant_auction n x p"
  shows "equilibrium_weakly_dominant_strategy n v (applicant_strategy_vector n v) x p"
proof -
  let ?b = "applicant_strategy_vector n v" (* the bids according to the strategy we want to prove optimal *)
  from val and aa have bids: "bids n ?b" using applicant_auction_def applicant_strategy_is_bid by simp
  from aa bids have alloc: "allocation n ?b x" unfolding applicant_auction_def by simp
  from aa bids have pay: "vickrey_payment n ?b p" unfolding applicant_auction_def by simp
  from aa have non_empty: "n > 0" unfolding applicant_auction_def by simp
  {
    fix i::participant
    assume i_range: "i \<in> {1..n}"
    fix whatever_bid::real_vector
    assume alternative_bid: "bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i"
    then have alternative_is_bid: "bids n whatever_bid" ..
    let ?i_sticks_with_strategy = "deviation_vec n whatever_bid ?b i"
      (* Agent i sticks to his/her strategy, whatever the others bid.  Given this, we have to show that agent i is best off. *)
    from bids alternative_is_bid
      have i_sticks_is_bid: "bids n ?i_sticks_with_strategy"
      by (simp add: deviated_bid_well_formed)
    have weak_dominance: "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i"
    proof - (* In contrast to Vickrey.vickreyA we don't have to consider the case "n=0", as applicant_auction_def requires n \<ge> 2. *)
      let ?b_bar = "maximum n ?b"
      show ?thesis
      proof cases (* case 1 of the short proof *)
        assume i_wins: "x ?i_sticks_with_strategy i"
        (* i gets the good, so i also satisfies the further properties of an applicant auction winner: *)
        with aa i_sticks_is_bid i_range
          have "i \<in> arg_max_set n ?i_sticks_with_strategy" by (metis allocated_implies_aa_winner second_price_auction_winner_def)
        then have "?i_sticks_with_strategy i = maximum n ?i_sticks_with_strategy" by (simp add: arg_max_set_def)
        also have "\<dots> \<ge> maximum_except n ?i_sticks_with_strategy i"
          using i_sticks_is_bid bids_def (* \<equiv> non_negative_real_vector n ?i_sticks_with_strategy *)
          non_empty i_range
          by (metis calculation maximum_greater_or_equal_remaining_maximum)
        finally have i_ge_max_except: "?i_sticks_with_strategy i \<ge> maximum_except n ?i_sticks_with_strategy i" by simp
        (* Now we show that i's payoff is \<ge> 0 *)
        from aa i_sticks_is_bid i_range i_wins have "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i
          = v i - maximum_except n ?i_sticks_with_strategy i" by (simp add: applicant_auction_winner_payoff)
oops

end

(*
        also have "\<dots> > ?i_sticks_with_strategy i - maximum_except n ?i_sticks_with_strategy i"
          unfolding applicant_strategy_vector_def deviation_vec_def deviation_def
          using val
          unfolding valuation_def using applicant_strategy_lt_valuation sledgehammer
        finally have payoff_expanded: "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i =
          ?i_sticks_with_strategy i - maximum_except n ?i_sticks_with_strategy i" by simp
        (* TODO CL: ask whether/how it is possible to name one step of a calculation (for reusing it) without breaking the chain (which is what we did here) *)
        also have "... \<ge> 0" using i_ge_max_except by simp
        finally have non_negative_payoff: "payoff_vector v (x ?i_sticks_with_strategy) (p ?i_sticks_with_strategy) i \<ge> 0" by simp
          
*)
