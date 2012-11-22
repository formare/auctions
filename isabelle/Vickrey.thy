(* TODO CL: ask whether jEdit's Isabelle mode disables word wrapping *)
(* TODO CL: report Isabelle/jEdit bug: no auto-indentation *)
(* TODO CL: report Isabelle/jEdit bug: when I set long lines to wrap at window boundary, wrapped part behaves badly: not editable *)
(* TODO CL: report Isabelle/jEdit bug: can't copy goal in output pane to clipboard *)
header {* Vickrey's Theorem:
Second price auctions support an equilibrium in weakly dominant strategies, and are efficient, if each participant bids their valuation of the good. *}

(*
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
imports Main Real

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

section{* Preliminaries *}

text{* some types defined for our convenience *}
type_synonym bool_vector = "nat \<Rightarrow> bool"
  (* TODO CL: report jEdit bug that suggested completions for nat (\<nat>) and bool (\<bool>) cause syntax errors *)
type_synonym real_vector = "nat \<Rightarrow> real"
type_synonym participant = "nat"  (* ordinal number *)
type_synonym participants = "nat" (* cardinal number *)

text{* TODO CL: discuss whether it's intuitive to name some types as in the following lines.
However, being of one such type does not yet imply well-formedness; e.g. we could have an x::allocation, which, for some given n and b does not satisfy "allocation n b x". *}
type_synonym allocation = "real_vector \<Rightarrow> participants \<Rightarrow> bool"
type_synonym payments = "real_vector \<Rightarrow> participants \<Rightarrow> real" (* a payment vector is a function of a real_vector of bids *)

subsection{* some range checks for vectors *}

text{* To ease writing, we introduce a predicate for the range of participants. *}
definition in_range ::
  "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "in_range n i \<equiv> 1 \<le> i \<and> i \<le> n"

text{* we could also, in a higher-order style, generally define a vector whose components satisfy a predicate, and then parameterise this predicate with $\geq 0$ and $> 0$ *}
definition non_negative_real_vector ::
  "nat \<Rightarrow> real_vector \<Rightarrow> bool" where
  "non_negative_real_vector n v \<equiv> \<forall> i::nat . in_range n i \<longrightarrow> v i \<ge> 0"

definition positive_real_vector ::
  "nat \<Rightarrow> real_vector \<Rightarrow> bool" where
  "positive_real_vector n v \<equiv> \<forall> i::nat . in_range n i \<longrightarrow> v i > 0"

section{* Deviation from a vector *}

text{* We define a function that modifies a vector by using an alternative value for a given component. *}
definition deviation ::
  "nat \<Rightarrow> real_vector \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "deviation n bid alternative_value index j \<equiv> if j = index then alternative_value else bid j"

text{* We define a function that,
  given one vector and an alternative one (in practice these will be strategy profiles), and a participant index i,
  returns a vector that
  has component i changed to the alternative value (i.e. in practice: the bid of participant i changed), whereas the others keep their original values.

  Actually this definition doesn't check whether its arguments are non-negative real vectors (i.e. well-formed strategy profiles). *}
(* NOTE CL: I changed the order of arguments compared to our original Theorema attempts, as I think this one is more intuitive.
   TODO CL: ask whether there a way of writing the alternative as b_hat, as it looks in the paper version?
   TODO CL: discuss whether there any useful way we could use n for range-checking?  Or don't we need n at all? *)
definition deviation_vec ::
  "nat \<Rightarrow> real_vector \<Rightarrow> real_vector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "deviation_vec n bid alternative_vec index \<equiv> deviation n bid (alternative_vec index) index"
  (* the old component-wise definition had an error actually:
     "deviation_vec n bid alternative_vec index j \<equiv> deviation n bid (alternative_vec j) index j"
                                                                                     ^^ should have been index
     so actually a component-wise definition was not necessary
     the error didn't cause trouble because of the "j = index" condition in deviation_def,
     but it prevented us from rewriting deviation_def into deviation without providing a component index, i.e. in curried form.
     The latter was desired after introducing remaining_maximum_invariant
       (which uses the more general "deviation" form instead of "deviation_vec") *)

section{* Strategy (bids) *}
text{*
Strategy and strategy profile (the vector of the strategies of all participants) are not fully defined below. We ignore the distribu-
tion and density function, as they do not play a role in the proof of the theorem.
So, for now, we do not model the random mapping from a participant's valuation to its bid, but simply consider its bid as a non-
negative number that doesn't depend on anything.
*}
definition bids ::
  "participants \<Rightarrow> real_vector \<Rightarrow> bool" where
  "bids n b \<equiv> non_negative_real_vector n b"

subsection{* Deviation from a bid *}

text{* A deviation from a bid is still a well-formed bid. *}
lemma deviated_bid_well_formed :
  fixes n::participants and bid::real_vector and alternative_vec::real_vector and i::participant
  assumes bids_original: "bids n bid" and bids_alternative: "bids n alternative_vec"
  shows "bids n (deviation_vec n bid alternative_vec i)"
proof -
  let ?dev = "deviation_vec n bid alternative_vec i"
  {
    fix k::participant
    assume k_range: "in_range n k"
    have "?dev k \<ge> 0"
    proof (cases "?dev k = bid k")
      case True
      with k_range and bids_original
        show ?thesis
        unfolding deviation_def
        by (simp only: bids_def non_negative_real_vector_def)
    next
      case False
      then have "?dev k = alternative_vec k" by (auto simp add: deviation_vec_def deviation_def)
           (* "then" \<equiv> "from this", where "this" is the most recently established fact;
             note that in line with https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2012-October/msg00057.html
             and for easier general comprehensibility
             we are not using the abbreviations "hence" \<equiv> "then have" and "thus" \<equiv> "then show" here. *)
        with k_range and bids_alternative show ?thesis unfolding deviation_def by (simp add: bids_def non_negative_real_vector_def)
    qed
  }
  then show "bids n ?dev" unfolding bids_def and non_negative_real_vector_def by simp
qed

text{* A single-good auction is a mechanism specified by a function that maps a strategy profile to an outcome. *}

section{* Allocation *}
text{* A function x, which takes a vector of n bids, is an allocation if it returns True for one bidder and False for the others. *}
(* TODO CL: discuss whether we should use different names for "definition allocation" and "type_synonym allocation", as they denote two different things *)
(* TODO CL: record in our notes that the order of arguments of a function matters.
   Note that I, CL, reordered the arguments on 2012-08-24.
   When using the function x in a curried way, we can speak of (x b) as a vector of booleans, in a very straightforward way;
   with a different order of arguments we'd have to use (\<lambda> index::nat . x index b).
*)
(* TODO CL: Discussion during Theorema formalisation: define this using a concrete x;
   just, in some theorems, _pass_ different x's into this definition, e.g. x1 := x(b), x2 := x(b')
   Same for payment *)
definition allocation :: "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> bool" where 
  "allocation n b x \<equiv> bids n b \<and> 
   (\<exists>k:: participant. in_range n k \<and> x b k \<and> (\<forall>j:: participant. j\<noteq>k \<longrightarrow> \<not>x b j))"

text{* An allocation function uniquely determines the winner. *}
lemma allocation_unique :
  fixes n::participants and x::allocation and b::real_vector and winner::participant
  assumes allocation: "allocation n b x"
    and winner: "x b winner"
  shows "x b j \<Longrightarrow> j = winner"
by (metis allocation allocation_def winner)

subsection{* Sample lemma: The allocation, in which the first participant wins (whatever the bids) is an allocation. *}

definition all_bid_1 :: "real_vector" where
   "all_bid_1 \<equiv> \<lambda>x.1"

(* TODO CL: document that, in contrast to Theorema, Isabelle can't _compute_ universal quantification in the finite case.
value "bids 1 all_bid_1"
*)

lemma bid_all_bid_1:
  shows "bids 1 all_bid_1"
  apply(unfold bids_def all_bid_1_def)
  apply(unfold non_negative_real_vector_def)
  apply(auto)
done

definition first_wins :: "allocation"
where
  "first_wins _ i \<equiv> i = 1" (* whatever the bids, the first participant wins *)

(* for testing
lemma only_wins_is_allocation:
  shows "allocation 1 all_bid_1 first_wins"
apply(unfold allocation_def)

apply(unfold first_wins_def)
apply(blast)
done
*)

(* TODO CL: note that this is a more tactic-free syntax; I think here it doesn't really make sense to write down explicit proof steps. *)
lemma only_wins_is_allocation_declarative:
  shows "allocation 1 all_bid_1 first_wins"
  unfolding allocation_def and in_range_def and first_wins_def using bid_all_bid_1
  by blast

section{* Payment *}

text{* Each participant pays some amount. *}
definition vickrey_payment ::
  "participants \<Rightarrow> real_vector \<Rightarrow> payments \<Rightarrow> bool" where
  "vickrey_payment n b p \<equiv> bids n b \<and> (\<forall>i:: participant. in_range n i \<longrightarrow> p b i \<ge> 0)"

section{* Outcome *}

text{* The outcome of an auction is specified an allocation ${0, 1}^n$ and a vector of payments $R^n$
 made by each participant; we don't introduce a dedicated definition for this. *}

section{* Valuation *}

text{* Each participant has a positive valuation of the good. *}
definition valuation ::
  "participants \<Rightarrow> real_vector \<Rightarrow> bool" where
  "valuation n v \<equiv> positive_real_vector n v"

text{* Any well-formed valuation vector is a well-formed bid vector *}
lemma valuation_is_bid :
  fixes n::participants and v::real_vector
  assumes "valuation n v"
  shows "bids n v"
(* Sledgehammer finds a proof
   by (metis assms bids_def non_negative_real_vector_def order_less_imp_le valuation_def)
   but we prefer manual Isar style here. *)
proof -
  {
    fix i::participant
    assume "in_range n i"
    with assms have "v i > 0" unfolding valuation_def and positive_real_vector_def by simp
    then have "v i \<ge> 0" by simp
      (* If we had been searching the library for an applicable theorem, we could have used
         find_theorems (200) "_ > _ \<Longrightarrow> _ \<ge> _" where 200 is some upper search bound,
         and would have found less_imp_le *)
  }
  then show "bids n v" unfolding bids_def and non_negative_real_vector_def by simp
qed

section{* Payoff *}

(* TODO CL: Maybe define payoff as a vector altogether, and just use one definition. *)
text{* The payoff of the winner ($x_i=1$), determined by a utility function u, is the difference between its valuation and the actual
payment. For the losers, it is the negative payment. *}
(* TODO CL: ask whether there is a built-in function that converts bool to {0,1} *)
definition payoff ::
  "real \<Rightarrow> bool \<Rightarrow> real \<Rightarrow> real" where
  "payoff Valuation Allocation Payment \<equiv> Valuation * (if Allocation then 1 else 0) - Payment"

(* for testing *)
value "payoff 5 True 2" (* I ascribed the value 5 to the good, won the auction, and had to pay 2. *)

text{* For convenience in the subsequent formalisation, we also define the payoff as a vector, component-wise. *}
definition payoff_vector ::
  "real_vector \<Rightarrow> bool_vector \<Rightarrow> real_vector \<Rightarrow> participant \<Rightarrow> real" where
  "payoff_vector v concrete_x concrete_p i \<equiv> payoff (v i) (concrete_x i) (concrete_p i)"

section{* Maximum and related functions *}
text{*
The maximum component value of a vector y of non-negative reals is equal to the value of one of the components, and it is greater or equal than the values of all [other] components.

We implement this as a computable function, whereas in Theorema we had two axioms:
1. The maximum component value is equal to the value of one of the components
2. maximum\_is\_greater\_or\_equal

Here, we derive those two statements as lemmas from the definition of the computable function.

Having the maximum as a computable function might turn out to be useful when doing concrete auctions.
*}
primrec maximum ::
  "nat \<Rightarrow> real_vector \<Rightarrow> real" where
  "maximum 0 _ = 0" |
  "maximum (Suc n) y = max 0 (max (maximum n y) (y (Suc n)))" (* we don't enforce that y is non-negative, but this computation only makes sense for a non-negative y *)

text{* If two vectors are equal, their maximum components are equal too *}
lemma maximum_equal :
  fixes n::nat and y::real_vector and z::real_vector
  shows "(\<forall>i::nat . in_range n i \<longrightarrow> y i = z i) \<longrightarrow> maximum n y = maximum n z"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof
    assume assms: "\<forall>i::nat . in_range (Suc n) i \<longrightarrow> y i = z i"
    then have equal_so_far: "maximum n y = maximum n z" by (simp add: Suc.hyps le_SucI in_range_def)
    from assms have equal_here: "y (Suc n) = z (Suc n)" using Suc.hyps by (metis Suc_eq_plus1 le_add2 le_refl in_range_def)
    with equal_so_far show "maximum (Suc n) y = maximum (Suc n) z" unfolding maximum_def by (simp add: Suc.hyps)
  qed
qed 

text{* The maximum component, as defined above, is non-negative *}
lemma maximum_non_negative :
  fixes n::nat and y::real_vector
  shows "maximum n y \<ge> 0"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "maximum (Suc n) y = max 0 (max (maximum n y) (y (Suc n)))" unfolding maximum_def by simp
  also have "\<dots> \<ge> 0" by auto
  finally show ?case .
qed

text{* The maximum component value is greater or equal than the values of all [other] components *}
lemma maximum_is_greater_or_equal :
  fixes n::nat and y::real_vector
  shows "\<forall> i::nat . in_range n i \<longrightarrow> maximum n y \<ge> y i"
proof (induct n)
  case 0
  show ?case by (simp add: in_range_def)
next
  case (Suc n)
  show ?case  
  (* This is a shorter alternative to first proving
     have "\<forall> i::nat . in_range (Suc n) i \<longrightarrow> maximum (Suc n) y \<ge> y i"
     and then trivially showing ?case *)
  proof
    fix i::nat
    show "in_range (Suc n) i \<longrightarrow> maximum (Suc n) y \<ge> y i"
    proof
      assume 1: "in_range (Suc n) i"
      have "max (maximum n y) (y (Suc n)) \<ge> y i" (* TODO CL: ask whether there is a way of automatically decomposing the initial goal until we arrive at this expression *)
      proof (cases "i = Suc n")
        case True
        then show ?thesis by (simp add: le_max_iff_disj)
      next
        case False
        with 1 (* TODO CL: ask whether there is a nicer way to write this, without having to number assumption 1 *)
          have "in_range n i" by (simp add: less_eq_Suc_le in_range_def)
        then have "maximum n y \<ge> y i" by (simp add: Suc.hyps)
        then show ?thesis by (simp add: le_max_iff_disj)
      qed
      then show "maximum (Suc n) y \<ge> y i" unfolding maximum_def by simp
    qed
  qed
qed

text{* The maximum component is one component *}
lemma maximum_is_component :
  fixes n::nat and y::real_vector
  shows "n > 0 \<and> non_negative_real_vector n y \<longrightarrow> (\<exists> i::nat . in_range n i \<and> maximum n y = y i)" (* reuse for "Suc n" inside proof didn't work when declaring premise with "assumes" *)
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof
    assume non_negative: "(Suc n) > 0 \<and> non_negative_real_vector (Suc n) y"
    show "\<exists> i::nat . in_range (Suc n) i \<and> maximum (Suc n) y = y i"
    proof (cases "y (Suc n) \<ge> maximum n y")
      case True
      from non_negative have "y (Suc n) \<ge> 0" unfolding in_range_def non_negative_real_vector_def by simp
      with True have "y (Suc n) = max 0 (max (maximum n y) (y (Suc n)))" by simp
      also have "\<dots> = maximum (Suc n) y" unfolding maximum_def by simp
      finally have "y (Suc n) = maximum (Suc n) y" .
      then show ?thesis using in_range_def by auto
    next
      case False
      have hyp: "n > 0 \<and> non_negative_real_vector n y \<longrightarrow> (\<exists> i::nat . in_range n i \<and> maximum n y = y i)" by (rule Suc.hyps)
      have non_empty: "n > 0"
      proof - (* by contradiction *)
        {
          assume "n = 0"
          with False and non_negative have "y (Suc n) = maximum n y"
            unfolding non_negative_real_vector_def maximum_def in_range_def
            by simp
          with False have "False" by simp
        }
        then show "n > 0" by blast
      qed
      from non_negative have pred_non_negative: "non_negative_real_vector n y"
        unfolding non_negative_real_vector_def in_range_def 
        by simp
      with non_empty and hyp obtain i::nat where pred_max: "in_range n i \<and> maximum n y = y i" by auto
      with non_negative have y_i_non_negative: "0 \<le> y i" unfolding non_negative_real_vector_def in_range_def by simp
      have "y i = maximum n y" using pred_max by simp
      also have "\<dots> = max (maximum n y) (y (Suc n))" using False by simp
        (* TODO CL: ask for the difference between "from" and "using" (before/after goal).
           In any case I got the impression that "with \<dots> also have" breaks the chain of calculational reasoning. *)
      also have "\<dots> = max 0 (max (maximum n y) (y (Suc n)))" using non_negative and y_i_non_negative by (auto simp add: calculation min_max.le_iff_sup)
      also have "\<dots> = maximum (Suc n) y" unfolding maximum_def using non_empty by simp
      finally have max: "y i = maximum (Suc n) y" .
      from pred_max have "in_range (Suc n) i" by (simp add: in_range_def)
      with max show ?thesis by auto
    qed
  qed
qed

text{* Being a component of a non-negative vector and being greater or equal than all other components uniquely defines a maximum component. *}
lemma maximum_sufficient :
  fixes n::nat and y::real_vector and m::real
  shows "non_negative_real_vector n y \<and> n > 0 \<and> (\<forall> i::nat . in_range n i \<longrightarrow> m \<ge> y i) \<and> (\<exists> i::nat . in_range n i \<and> m = y i) \<longrightarrow> m = maximum n y"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof
    assume assms: "non_negative_real_vector (Suc n) y \<and> Suc n > 0 \<and> (\<forall> i::nat . in_range (Suc n) i \<longrightarrow> m \<ge> y i) \<and> (\<exists> i::nat . in_range (Suc n) i \<and> m = y i)"
    (* now break this down into its conjunctives *)
    from assms have non_negative: "non_negative_real_vector (Suc n) y" ..
      (* ".." means: apply a canonical rule for the current context *)
    from assms have non_empty: "Suc n > 0" by simp
    from assms have greater_or_equal: "\<forall> i::nat . in_range (Suc n) i \<longrightarrow> m \<ge> y i" by simp
    from assms have is_component: "\<exists> i::nat . in_range (Suc n) i \<and> m = y i" by simp
    (* further preliminaries *)
    from non_negative have pred_non_negative: "non_negative_real_vector n y"
      unfolding non_negative_real_vector_def in_range_def by simp
    (* then go on *)
    from non_empty have max_def: "maximum (Suc n) y = max 0 (max (maximum n y) (y (Suc n)))" unfolding maximum_def by simp
    also have "\<dots> = m"
    proof (cases "n = 0")
      case True
      with is_component have m_is_only_component: "m = y 1" unfolding in_range_def by auto
      with non_negative have "m \<ge> 0" unfolding non_negative_real_vector_def in_range_def by simp
      (* we could break this down into further textbook-style steps, but their proofs turn out to be ugly as well, so we leave it at this high level *)
      then have "max 0 (max (maximum 0 y) (y 1)) = m" by (auto simp add: m_is_only_component)
      with True show ?thesis by auto (* this was (metis One_nat_def), but auto has access to simplification rules by default *)
    next
      case False
      show ?thesis
      proof cases
        assume last_is_max: "y (Suc n) = m"
        have "\<dots> \<ge> maximum n y"
        proof -
          from False and pred_non_negative and maximum_is_component have "\<exists> k::nat . in_range n k \<and> maximum n y = y k" by auto
          then obtain k::nat where "in_range n k \<and> maximum n y = y k" by auto
          with greater_or_equal show ?thesis unfolding in_range_def by (simp add: le_Suc_eq)
            (* TODO CL: ask whether we should have kept using metis here.  Sledgehammer always suggests metis.
               When auto or simp also works (which is the case here, but not always), is is more efficient? *)
        qed
        then show ?thesis using last_is_max by (metis less_max_iff_disj linorder_not_le maximum_non_negative min_max.sup_absorb1 min_max.sup_commute)
      next
        assume "y (Suc n) \<noteq> m"
        with is_component have pred_is_component: "\<exists>k::nat . in_range n k \<and> m = y k"
          unfolding in_range_def by (metis le_antisym not_less_eq_eq)
        from greater_or_equal have "\<forall>k::nat . in_range n k \<longrightarrow> m \<ge> y k" unfolding in_range_def by simp
        (* these, plus pred_non_negative, form the left hand side of the induction hypothesis *)
        then have "m = maximum n y" by (metis False Suc gr0I pred_is_component pred_non_negative)
        then show ?thesis
          using in_range_def by (metis Suc_eq_plus1 greater_or_equal le_refl maximum_non_negative min_max.sup_absorb1 min_max.sup_absorb2 not_add_less2 not_leE)
      qed
    qed
    finally show "m = maximum (Suc n) y" ..
  qed
qed

(* TODO CL: discuss whether it makes sense to keep this lemma – it's not used for "theorem vickreyA" but might still be useful for the toolbox *)
text{* Increasing the (actually: a) maximum component value keeps it the maximum. *}
lemma increment_keeps_maximum :
  fixes n::nat and y::real_vector and y'::real_vector and max_index::nat and max::real and max'::real
  assumes non_negative: "non_negative_real_vector n y"
    and non_empty: "n > 0"
    and index_range: "in_range n max_index"
    and old_maximum: "maximum n y = y max_index"
    and new_lt: "y max_index < max'"
    and increment: "y' = (\<lambda> i::nat . if i = max_index then max' else y i)"
  shows "maximum n y' = y' max_index"
proof -
  from increment have new_component: "y' max_index = max'" by simp
  from non_negative and index_range and new_lt have "\<dots> \<ge> 0" unfolding non_negative_real_vector_def by (auto simp add: linorder_not_less order_less_trans)
  with non_negative and increment have new_non_negative: "non_negative_real_vector n y'" unfolding non_negative_real_vector_def by simp
  from old_maximum and new_lt and increment
    have greater_or_equal: "\<forall> i::nat . in_range n i \<longrightarrow> max' \<ge> y' i"
    by (metis linorder_not_less maximum_is_greater_or_equal order_less_trans order_refl)
  from increment have "max' = y' max_index" by simp
  (* now we have all prerequisites for applying maximum_sufficient *)
  with new_non_negative and non_empty and greater_or_equal and index_range
    show "maximum n y' = y' max_index" using maximum_sufficient by metis
qed 

text{* a test vector whose maximum component value we determine *}
value "maximum 2 (\<lambda> x::nat . 1)"
value "maximum 5 (\<lambda> x::nat . x)"

text{* We define the set of maximal components of a vector y: *}
(* TODO CL: discuss whether we should define this in a computable way.  If so, how? *)
(* TODO CL: discuss whether this function should return a set, or a vector.  How to construct such a vector?  Or should we define it as a predicate? *)
definition arg_max_set ::
  "nat \<Rightarrow> real_vector \<Rightarrow> (nat set)" where
  "arg_max_set n b \<equiv> {i. in_range n i \<and> maximum n b = b i}"

(* for testing *)
lemma test_arg_max_set:
  shows "{1,2} \<subseteq> arg_max_set 3 (\<lambda>x. if x < 3 then 100 else 0)" (* the 1st and 2nd elements in a vector [100,100,\<dots>] are maximal. *)
apply(unfold arg_max_set_def in_range_def)
apply(simp add: maximum_def)
done

text{* an alternative proof of the same lemma – still too trivial to test how declarative proofs \emph{actually} work *}
lemma test_arg_max_set_declarative:
  shows "{1,2} \<subseteq> arg_max_set 3 (\<lambda>x. if x < 3 then 100 else 0)" (* the 1st and 2nd elements in a vector [100,100,\<dots>] are maximal. *)
unfolding arg_max_set_def in_range_def
  by (simp add: maximum_def)

text{* constructing a new vector from a given one, by skipping one component *}
definition skip_index ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "skip_index vector index = (\<lambda> i::nat . vector (if i < index then i else Suc i))"

text{* skipping one component in a non-negative vector keeps it non-negative *}
(* TODO CL: discuss whether we should actually prove the more general lemma that
   skipping one component in a vector whose components each satisfy p still satisfies p (for a suitable p) *)
lemma skip_index_keeps_non_negativity :
  fixes n::nat and v::real_vector and i::nat
  assumes non_empty: "n > 0"
    and non_negative: "non_negative_real_vector n v"
    and range: "in_range n i"
  shows "non_negative_real_vector (n-(1::nat)) (skip_index v i)"
proof -
  {
    fix j::nat
    have "in_range (n-(1::nat)) j \<longrightarrow> (skip_index v i) j \<ge> 0"
    proof
      assume j_range: "in_range (n-(1::nat)) j"
      show "(skip_index v i) j \<ge> 0"
      proof (cases "j < i")
        case True
        then have "(skip_index v i) j = v j" unfolding skip_index_def by simp
        with j_range and non_negative show ?thesis
          unfolding non_negative_real_vector_def in_range_def
          by (auto simp add: leD less_imp_diff_less not_leE)
      next
        case False
        then have "(skip_index v i) j = v (Suc j)" unfolding skip_index_def by simp
        with j_range and non_negative show ?thesis
          unfolding non_negative_real_vector_def in_range_def
          by (auto simp add: leD less_imp_diff_less not_leE)
      qed
    qed
  }
  then show "non_negative_real_vector (n-(1::nat)) (skip_index v i)" unfolding non_negative_real_vector_def by simp
qed

text{* when two vectors differ in one component, skipping that component makes the vectors equal *}
lemma equal_by_skipping :
  fixes n::nat and v::real_vector and w::real_vector and j::nat and k::nat
  assumes non_empty: "n > 0"
    and j_range: "in_range n j"
    and equal_except: "\<forall>i::nat . in_range n i \<and> i \<noteq> j \<longrightarrow> v i = w i"
    and k_range: "in_range (n-(1::nat)) k"
  shows "(skip_index v j) k = (skip_index w j) k"
proof (cases "k < j")
  case True
  then have "(skip_index v j) k = v k" 
    and "(skip_index w j) k = w k"
    unfolding skip_index_def by auto
  with equal_except and k_range and True show ?thesis
    using in_range_def by (metis diff_le_self le_trans less_not_refl)
next
  case False
  then have "(skip_index v j) k = v (Suc k)"
    and "(skip_index w j) k = w (Suc k)"
    unfolding skip_index_def by auto
  with equal_except and k_range and False show ?thesis
   using in_range_def
   by (metis One_nat_def diff_0_eq_0 diff_Suc_Suc diff_less le_neq_implies_less lessI less_imp_diff_less linorder_not_less not_less_eq_eq)
qed

text{* We define the maximum component value that remains after removing the i-th component from the non-negative real vector y: *}
(* TODO CL: discuss whether we should demand n \<ge> 2, or whether it's fine to implicitly assume that maximum_except 1 y j is 0
   (= the "second highest bid" when there is only one bidder) *)
(* TODO CL: discuss whether we can, or should, enforce that j is \<le> n *)
(* TODO CL: ask whether there is an easier or more efficient way of stating this *)
primrec maximum_except ::
  "nat \<Rightarrow> real_vector \<Rightarrow> nat \<Rightarrow> real" where
  "maximum_except 0 _ _ = 0" |
  "maximum_except (Suc n) y j =
    maximum n (skip_index y j)" (* we take y but skip its j-th component *)

(* for testing *)
value "maximum_except 3 (\<lambda> x::nat . 4-x) 1" (* the maximum component value of the vector [3,2,1], except the first element, is 2 *)

text{* The maximum component that remains after removing one component from a vector is greater or equal than the values of all remaining components *}
lemma maximum_except_is_greater_or_equal :
  fixes n::nat and y::real_vector and j::nat and i::nat
  assumes j_range: "n \<ge> 1 \<and> in_range n j"
    and i_range: "in_range n i \<and> i \<noteq> j"
  shows "maximum_except n y j \<ge> y i"
proof -
  let ?y_with_j_skipped = "skip_index y j"
  from j_range obtain pred_n where pred_n: "n = Suc pred_n"
    by (metis not0_implies_Suc not_one_le_zero)
    (* wouldn't work with simp or rule alone *)
  then show "maximum_except n y j \<ge> y i"
  proof (cases "i < j")
    case True
    then have can_skip_j: "y i = ?y_with_j_skipped i" unfolding skip_index_def by simp
    from True and j_range and i_range and pred_n have "in_range pred_n i" unfolding in_range_def by simp
    then have "maximum pred_n ?y_with_j_skipped \<ge> ?y_with_j_skipped i" by (simp add: maximum_is_greater_or_equal)
    with can_skip_j and pred_n show ?thesis by simp
  next
    case False
    with i_range have case_False_nice: "i > j" by simp
    then obtain pred_i where pred_i: "i = Suc pred_i" by (rule lessE) (* TODO CL: ask why this works.  I do not really understand what lessE does. *)
    from case_False_nice and pred_i (* wouldn't work with "from False" *)
      have can_skip_j_and_shift_left: "y i = ?y_with_j_skipped pred_i" unfolding skip_index_def by simp
    from case_False_nice and i_range and j_range and pred_i and pred_n
      have (* actually 2 \<le> i, but we don't need this *) "in_range pred_n pred_i" unfolding in_range_def by simp
    then have "maximum pred_n ?y_with_j_skipped \<ge> ?y_with_j_skipped pred_i" by (simp add: maximum_is_greater_or_equal)
    with can_skip_j_and_shift_left and pred_n show ?thesis by simp
  qed
qed

text{* One component of a vector is a maximum component iff it has a value greater or equal than the maximum of the remaining values. *}
lemma maximum_greater_or_equal_remaining_maximum :
  (* TODO CL: discuss the name of this lemma; maybe there is something more appropriate *)
  fixes n::nat and y::real_vector and j::nat
  assumes non_negative: "non_negative_real_vector n y"
    and non_empty: "n > 0"
    and range: "in_range n j"
  shows "y j \<ge> maximum_except n y j \<longleftrightarrow> y j = maximum n y"
proof
  assume ge_remaining: "y j \<ge> maximum_except n y j"
  from non_empty and range have "\<forall> i::nat . in_range n i \<and> i \<noteq> j \<longrightarrow> maximum_except n y j \<ge> y i" by (simp add: maximum_except_is_greater_or_equal)
  with ge_remaining have "\<forall> i::nat . in_range n i \<and> i \<noteq> j \<longrightarrow> y j \<ge> y i" by auto
  then have greater_or_equal: "\<forall> i::nat . in_range n i \<longrightarrow> y j \<ge> y i" by auto
  from range have is_component: "\<exists> i::nat . in_range n i \<and> y j = y i" by auto
    (* when we first tried non_empty: "n \<ge> 1" sledgehammer didn't find a proof for this *)
  with non_negative and non_empty and greater_or_equal show "y j = maximum n y" by (simp add: maximum_sufficient)
  (* TODO CL: ask whether it makes a difference to use "by auto" vs. "by simp" (or even "by arith") when either would work,
              and what's the difference between "from foo show bar by simp" vs. "show bar by (simp add: foo)" *)
next (* nice to see that support for \<longleftrightarrow> is built in *)
  assume j_max: "y j = maximum n y"
  from non_empty
    have maximum_except_unfolded: "maximum_except n y j = maximum (n-(1::nat)) (skip_index y j)"
    by (metis Suc_diff_1 maximum_except.simps(2))
  show "y j \<ge> maximum_except n y j"
  proof (cases "n = 1")
    case True
    with maximum_except_unfolded and maximum_def have "maximum_except n y j = 0" by auto
    with j_max and non_negative show ?thesis by (simp add: maximum_non_negative)
  next
    case False
    from j_max have ge: "\<forall>k::nat . in_range n k \<longrightarrow> y j \<ge> y k" by (simp add: maximum_is_greater_or_equal)
    from False and non_empty have "n > 1" by auto
    then have pred_non_empty: "(n-(1::nat)) > 0" by simp
    from non_empty and non_negative and range have pred_non_negative: "non_negative_real_vector (n-(1::nat)) (skip_index y j)"
      by (metis skip_index_keeps_non_negativity)
    from pred_non_empty and pred_non_negative and maximum_is_component
      have "\<exists> i::nat . in_range (n-(1::nat)) i \<and> maximum (n-(1::nat)) (skip_index y j) = (skip_index y j) i" by simp
    then obtain i::nat where maximum_except_component: "in_range (n-(1::nat)) i \<and> maximum (n-(1::nat)) (skip_index y j) = (skip_index y j) i" ..
    then have i_range: "in_range (n-(1::nat)) i" ..
    from maximum_except_component and maximum_except_unfolded
      have maximum_except_component_nice: "maximum_except n y j = (skip_index y j) i" by simp
    have skip_index_range: "\<dots> = y i \<or> (skip_index y j) i = y (Suc i)" unfolding skip_index_def by auto
    from i_range have 1: "in_range n i" unfolding in_range_def by arith
    from i_range have 2: "in_range n (Suc i)" unfolding in_range_def by arith
    from skip_index_range and 1 and 2 have "\<exists> k::nat . in_range n k \<and> (skip_index y j) i = y k" by auto
    (* The following (found by remote_vampire) was nearly impossible for metis to prove: *)
    (* from i_range and range and skip_index_def
      and maximum_except_component (* not sure why we need this given that we have maximum_except_component *)
      have "\<exists> k::nat . in_range n k \<and> (skip_index y j) i = y k"
      by (metis (full_types) One_nat_def Suc_neq_Zero Suc_pred' leD less_Suc0 less_Suc_eq_le linorder_le_less_linear) *)
    then obtain k::nat where "in_range n k \<and> (skip_index y j) i = y k" ..
    with ge and maximum_except_component_nice show "y j \<ge> maximum_except n y j" by simp
  qed
qed

text{* Changing one component in a vector doesn't affect the maximum of the remaining components. *}
lemma remaining_maximum_invariant :
  (* TODO CL: discuss the name of this lemma; maybe there is something more appropriate *)
  fixes n::nat and y::real_vector and i::nat and a::real
  assumes non_empty: "n > 0" and
    range: "in_range n i"
  shows "maximum_except n y i = maximum_except n (deviation n y a i) i"
proof -
  from range have "\<forall>j::nat . in_range n j \<and> j \<noteq> i \<longrightarrow> y j = deviation n y a i j"
    unfolding deviation_def by simp
  with non_empty and range
    have "\<forall>k::nat . in_range (n-(1::nat)) k \<longrightarrow> skip_index y i k = skip_index (deviation n y a i) i k"
    by (simp add: equal_by_skipping)
  then have "maximum (n-(1::nat)) (skip_index y i) = maximum (n-(1::nat)) (skip_index (deviation n y a i) i)"
    by (simp add: maximum_equal)
  with non_empty show ?thesis by (metis Suc_pred' maximum_except.simps(2))
qed

section{* Second-price auction *}

text{* Agent i being the winner of a second-price auction (see below for complete definition) means
* he/she is one of the participants with the highest bids
* he/she wins the auction
* and pays the maximum price that remains after removing the winner's own bid from the vector of bids. *}
definition second_price_auction_winner ::
  "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool" where
  "second_price_auction_winner n b x p i \<equiv> in_range n i \<and> i \<in> arg_max_set n b \<and> x b i \<and> (p b i = maximum_except n b i)"

text{* Agent i being a loser of a second-price auction (see below for complete definition) means
* he/she loses the auction
* and pays nothing *}
definition second_price_auction_loser ::
  "participants \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> participant \<Rightarrow> bool" where
  "second_price_auction_loser n b x p i \<equiv> in_range n i \<and> \<not>x b i \<and> p b i = 0"

text{* A second-price auction is an auction whose outcome satisfies the following conditions:
1. One of the participants with the highest bids wins. (We do not formalise the random selection of one distinct participants from the set of highest bidders,
in case there is more than one.)
2. The price that the winner pays is the maximum bid that remains after removing the winner's own bid from the vector of bids.
3. The losers do not pay anything. *}
definition second_price_auction ::
  "participants \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool" where
  "second_price_auction n x p \<equiv>
    \<forall> b::real_vector . bids n b \<longrightarrow> allocation n b x \<and> vickrey_payment n b p \<and>
    (\<exists>i::participant. in_range n i \<and> second_price_auction_winner n b x p i
                      \<and> (\<forall>j::participant. in_range n j \<and> j \<noteq> i \<longrightarrow> second_price_auction_loser n b x p j))"

(* TODO CL: structure as in Theorema: \<forall>i \<forall>j . ... \<longrightarrow> i = j *)
text{* We chose not to \emph{define} that a second-price auction has only one winner, as it is not necessary.  Therefore we have to prove it. *}
lemma second_price_auction_has_only_one_winner :
  fixes n::participants and x::allocation and p::payments and b::real_vector and winner::participant and j::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and winner: "second_price_auction_winner n b x p winner"
    and also_winner: "second_price_auction_winner n b x p j"
  shows "j = winner"
proof -
  from winner have wins: "x b winner" by (simp add: second_price_auction_winner_def)
  from also_winner have j_wins: "x b j" by (simp add: second_price_auction_winner_def)
  from spa and bids have "allocation n b x" by (simp add: second_price_auction_def)
  with wins and j_wins show "j = winner" by (simp add: allocation_unique)
qed

text{* The participant who gets the good also satisfies the further properties of a second-price auction winner *}
lemma allocated_implies_spa_winner :
  fixes n::participants and x::allocation and p::payments and b::real_vector and winner::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and wins: "x b winner" (* note that we need not assume anything about the range of winner *)
  shows "second_price_auction_winner n b x p winner"
proof -
  from wins and spa and bids and second_price_auction_winner_def and second_price_auction_has_only_one_winner
  show ?thesis by (metis allocation_unique second_price_auction_def)
qed

text{* A participant who doesn't gets the good satisfies the further properties of a second-price auction loser *}
lemma not_allocated_implies_spa_loser :
  fixes n::participants and x::allocation and p::payments and b::real_vector and loser::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "in_range n loser"
    and loses: "\<not> x b loser"
  shows "second_price_auction_loser n b x p loser"
proof - (* by contradiction *)
  {
    assume False: "\<not> second_price_auction_loser n b x p loser"
    from spa and bids and second_price_auction_def
      have "(\<exists>j::participant. in_range n j \<and> second_price_auction_winner n b x p j
                  \<and> (\<forall>k::participant. in_range n k \<and> k \<noteq> j \<longrightarrow> second_price_auction_loser n b x p k))" by simp
    with False and range have "second_price_auction_winner n b x p loser" by auto
      (* Before we had introduced in_range as a predicate consistently used both in the winner and the loser branch,
         even metis wan't able to prove this without exceeding the unification bound. *)
    with second_price_auction_winner_def have "x b loser" by simp
    with loses have "False" ..
  }
  then show ?thesis by blast
qed

text{* If there is only one bidder with a maximum bid, that bidder wins. *}
lemma only_max_bidder_wins :
  fixes n::participants and max_bidder::participant and b::real_vector and x::allocation and p::payments
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "in_range n max_bidder"
    (* and max_bidder: "b max_bidder = maximum n b" *) (* we actually don't need this :-) *)
    and only_max_bidder: "b max_bidder > maximum_except n b max_bidder"
  shows "second_price_auction_winner n b x p max_bidder"
proof -
  have no_other_max: "\<forall>j::participant. in_range n j \<and> j \<noteq> max_bidder \<longrightarrow> j \<notin> arg_max_set n b"
  proof
    fix j::participant
    show "in_range n j \<and> j \<noteq> max_bidder \<longrightarrow> j \<notin> arg_max_set n b"
    proof
      assume j_not_max: "in_range n j \<and> j \<noteq> max_bidder"
      show "j \<notin> arg_max_set n b"
      proof -
        from j_not_max and range have "b j \<le> maximum_except n b max_bidder"
          using in_range_def maximum_except_is_greater_or_equal by (metis le_trans)
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
    qed
  qed
  from bids and spa
    have x_is_allocation: "\<exists>i:: participant. in_range n i \<and> x b i \<and> (\<forall>j:: participant. j\<noteq>i \<longrightarrow> \<not>x b j)"
    unfolding second_price_auction_def allocation_def in_range_def by simp
  from bids and spa have "\<exists>i::participant. second_price_auction_winner n b x p i
    \<and> (\<forall>j::participant. in_range n j \<and> j \<noteq> i \<longrightarrow> second_price_auction_loser n b x p j)" unfolding second_price_auction_def by blast
  with (* max_bidder and *) (* turns out that we didn't need this :-) *)
    no_other_max and x_is_allocation show ?thesis by (metis (full_types) second_price_auction_winner_def)
qed

text{* a formula for computing the payoff of the winner of a second-price auction *}
lemma second_price_auction_winner_payoff :
  fixes n::participants and v::real_vector and x::allocation and b::real_vector and p::payments and winner::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and wins: "x b winner"
  shows "payoff_vector v (x b) (p b) winner = v winner - maximum_except n b winner"
proof -
  have "payoff_vector v (x b) (p b) winner
    = payoff (v winner) (x b winner) (p b winner)" unfolding payoff_vector_def by simp
  also have "\<dots> = payoff (v winner) True (p b winner)" using wins by simp
  also have "\<dots> = v winner - p b winner" unfolding payoff_def by simp
  also have "\<dots> = v winner - maximum_except n b winner"
    using wins and spa and bids by (metis allocated_implies_spa_winner second_price_auction_winner_def)
  finally show ?thesis by simp
qed

text{* a formula for computing the payoff of a loser of a second-price auction *}
lemma second_price_auction_loser_payoff :
  fixes n::participants and v::real_vector and x::allocation and b::real_vector and p::payments and loser::participant
  assumes spa: "second_price_auction n x p"
    and bids: "bids n b"
    and range: "in_range n loser"
    and loses: "\<not> x b loser"
  shows "payoff_vector v (x b) (p b) loser = 0"
proof -
  from loses and spa and bids and range
    have "second_price_auction_loser n b x p loser"
    by (simp add: not_allocated_implies_spa_loser)
  then show ?thesis unfolding second_price_auction_loser_def payoff_vector_def payoff_def
    by (metis (full_types) diff_0_right mult_zero_right)
qed

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
    and range: "in_range n winner"
    and wins: "x b winner"
  shows "let winner_sticks_with_valuation = deviation_vec n b v winner
    in payoff_vector v (x b) (p b) winner = v winner - maximum_except n winner_sticks_with_valuation winner"
proof -
  let ?winner_sticks_with_valuation = "deviation_vec n b v winner"
  (* winner gets the good, so winner also satisfies the further properties of a second price auction winner: *)
  from wins and spa and bids
    have "payoff_vector v (x b) (p b) winner = v winner - maximum_except n b winner"
    by (simp add: second_price_auction_winner_payoff)
  (* i's deviation doesn't change the maximum remaining bid (which is the second highest bid when winner wins) *)
  also have "\<dots> = v winner - maximum_except n ?winner_sticks_with_valuation winner"
    unfolding deviation_vec_def using non_empty and range and remaining_maximum_invariant by auto
  finally show ?thesis by simp
qed

section{* Efficiency *}

text{* A single good auction (this is the one we are talking about here) is efficient, if the winner is among the participants who have the
highest valuation of the good. *}
definition efficient ::
  "participants \<Rightarrow> real_vector \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> bool" where
  "efficient n v b x \<equiv> (valuation n v \<and> bids n b) \<and>
      (\<forall>i::participant. in_range n i \<and> x b i \<longrightarrow> i \<in> arg_max_set n v)"

section{* Equilibrium in weakly dominant strategies *}

text{* Given some auction, a strategy profile supports an equilibrium in weakly dominant strategies
  if each participant maximises its payoff by playing its component in that profile,
    whatever the other participants do. *}
definition equilibrium_weakly_dominant_strategy ::
  "participants \<Rightarrow> real_vector \<Rightarrow> real_vector \<Rightarrow> allocation \<Rightarrow> payments \<Rightarrow> bool" where
  "equilibrium_weakly_dominant_strategy n v b x p \<equiv>
    (* TODO CL: note that 'bids n b' is actually redundant, as allocation and vickrey_payment require bids. *)
    valuation n v \<and> bids n b \<and> allocation n b x \<and> vickrey_payment n b p \<and> 
   (\<forall> i::participant . in_range n i \<longrightarrow>
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
  from val have bids: "bids n v" by (rule valuation_is_bid)
  have equilibrium_weakly_dominant_strategy_unfolded:
    "\<forall> i::participant . in_range n i \<longrightarrow>
      (\<forall> whatever_bid::real_vector . bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i \<longrightarrow> (
       let i_sticks_with_valuation = deviation_vec n whatever_bid ?b i
         in payoff_vector v (x i_sticks_with_valuation) (p i_sticks_with_valuation) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i))"
  proof
    fix i::participant
    show "in_range n i \<longrightarrow> (\<forall> whatever_bid::real_vector. bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i
      \<longrightarrow> (let i_sticks_with_valuation = deviation_vec n whatever_bid ?b i
      in payoff_vector v (x i_sticks_with_valuation) (p i_sticks_with_valuation) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i))"
    proof (cases "n = 0")
      case True
      then show ?thesis by (simp add: in_range_def)
    next
      case False
      then have non_empty: "n > 0" ..
      show ?thesis
      proof
        assume i_range: "in_range n i"
        let ?b_bar = "maximum n ?b"
        show "\<forall> whatever_bid::real_vector. bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i \<longrightarrow> (let i_sticks_with_valuation = deviation_vec n whatever_bid ?b i
          in payoff_vector v (x i_sticks_with_valuation) (p i_sticks_with_valuation) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i)"
        proof
          fix whatever_bid::real_vector
          let ?i_sticks_with_valuation = "deviation_vec n whatever_bid ?b i"
            (* Agent i sticks to bidding his/her valuation, whatever the others bid.  Given this, we have to show that agent i is best off. *)
          have "bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i \<longrightarrow>
            payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i"
          proof
            assume alternative_bid: "bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i"
            then have alternative_is_bid: "bids n whatever_bid" ..
            from bids and alternative_is_bid
              have i_sticks_is_bid: "bids n ?i_sticks_with_valuation"
              by (simp add: deviated_bid_well_formed)
            (* interesting part starts here *)
            show "payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i"
            proof cases (* case 1 of the short proof *)
              assume i_wins: "x ?i_sticks_with_valuation i"
              (* i gets the good, so i also satisfies the further properties of a second price auction winner: *)
              with spa and i_sticks_is_bid
                have "i \<in> arg_max_set n ?i_sticks_with_valuation" by (metis allocated_implies_spa_winner second_price_auction_winner_def)
              (* TODO CL: ask whether it is possible to get to "have 'a' and 'b'" directly,
                 without first saying "have 'a \<and> b' and then breaking it down "by auto".
                 In an earlier version we had not only deduced i_in_max_set but also the payoff here. *)
              then have "?i_sticks_with_valuation i = maximum n ?i_sticks_with_valuation" by (simp add: arg_max_set_def)
              also have "\<dots> \<ge> maximum_except n ?i_sticks_with_valuation i"
                using i_sticks_is_bid and bids_def (* \<equiv> non_negative_real_vector n ?i_sticks_with_valuation *)
                and non_empty and i_range
                by (metis calculation maximum_greater_or_equal_remaining_maximum)
              finally have i_ge_max_except: "?i_sticks_with_valuation i \<ge> maximum_except n ?i_sticks_with_valuation i" by auto
              (* Now we show that i's payoff is \<ge> 0 *)
              from spa and i_sticks_is_bid and i_wins have "payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i
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
                with spa and alternative_is_bid and non_empty and i_range
                  have "payoff_vector v (x whatever_bid) (p whatever_bid) i = ?i_sticks_with_valuation i - maximum_except n ?i_sticks_with_valuation i"
                  using winners_payoff_on_deviation_from_valuation by (metis deviation_vec_def deviation_def)
                (* Now we show that i's payoff hasn't changed *)
                also have "\<dots> = payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i"
                  using payoff_expanded by simp
                finally show ?thesis by simp (* = \<longrightarrow> \<le> *)
              next (* case 1b of the short proof *)
                assume "\<not> x whatever_bid i"
                (* i doesn't get the good, so i also satisfies the further properties of a second price auction loser: *)
                with spa and alternative_is_bid and i_range
                  have "payoff_vector v (x whatever_bid) (p whatever_bid) i = 0"
                  by (rule second_price_auction_loser_payoff)
                also have "\<dots> \<le> payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i" using non_negative_payoff by simp
                finally show ?thesis by simp
              qed
            next (* case 2 of the short proof *)
              assume i_loses: "\<not> x ?i_sticks_with_valuation i"
              (* i doesn't get the good, so i's payoff is 0 *)
              with spa and i_sticks_is_bid and i_range
                have zero_payoff: "payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i = 0"
                by (rule second_price_auction_loser_payoff)
              (* i's bid can't be higher than the second highest bid, as otherwise i would have won *)
              have i_bid_at_most_second: "?i_sticks_with_valuation i \<le> maximum_except n ?i_sticks_with_valuation i"
              proof - (* by contradiction *)
                {
                  assume "\<not> ?i_sticks_with_valuation i \<le> maximum_except n ?i_sticks_with_valuation i"
                  then have "?i_sticks_with_valuation i > maximum_except n ?i_sticks_with_valuation i" by simp
                  with spa and i_sticks_is_bid and i_range
                    have "second_price_auction_winner n ?i_sticks_with_valuation x p i"
                    using only_max_bidder_wins (* a lemma we had from the formalisation of the earlier 10-case proof *)
                    by auto
                  with i_loses have False using second_price_auction_winner_def by auto
                }
                then show ?thesis by blast
              qed
              show ?thesis
              proof cases (* case 2a of the short proof *)
                assume "x whatever_bid i"
                with spa and alternative_is_bid and non_empty and i_range
                  have "payoff_vector v (x whatever_bid) (p whatever_bid) i = ?i_sticks_with_valuation i - maximum_except n ?i_sticks_with_valuation i"
                  using winners_payoff_on_deviation_from_valuation by (metis deviation_vec_def deviation_def)
                (* Now we can compute i's payoff *)
                also have "\<dots> \<le> 0" using i_bid_at_most_second by arith
                also have "\<dots> = payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i"
                  using zero_payoff by arith
                finally show ?thesis by auto
              next (* case 2b of the short proof *)
                assume "\<not> x whatever_bid i"
                (* i doesn't get the good, so i's payoff is 0 *)
                with spa and alternative_is_bid and i_range
                  have "payoff_vector v (x whatever_bid) (p whatever_bid) i = 0"
                  by (rule second_price_auction_loser_payoff)
                also have "\<dots> = payoff_vector v (x ?i_sticks_with_valuation) (p ?i_sticks_with_valuation) i" using zero_payoff by simp
                finally show ?thesis by simp
              qed
            qed
          qed
          then show "bids n whatever_bid \<and> whatever_bid i \<noteq> ?b i
          \<longrightarrow> (let i_sticks_with_valuation = deviation_vec n whatever_bid ?b i
          in payoff_vector v (x i_sticks_with_valuation) (p i_sticks_with_valuation) i \<ge> payoff_vector v (x whatever_bid) (p whatever_bid) i)"
            (* TODO CL: ask why ?thesis doesn't work here *)
            by simp
        qed
      qed
    qed
  qed
  with spa val bids second_price_auction_def show ?thesis unfolding equilibrium_weakly_dominant_strategy_def by auto
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
  have efficient_def_unfolded: "\<forall>k::participant. in_range n k \<and> x ?b k \<longrightarrow> k \<in> arg_max_set n v" unfolding efficient_def
  proof
    fix k:: participant
    show "in_range n k \<and> x ?b k \<longrightarrow> k \<in> arg_max_set n v"
    proof
      assume (* k_wins: *)"in_range n k \<and> x ?b k"
      with spa and bids show "k \<in> arg_max_set n v"
        using allocated_implies_spa_winner second_price_auction_winner_def by auto
      (* alternative proof with fewer prerequisites (before we had the lemmas used above): *)
      (* show "k \<in> arg_max_set n v"
      proof -
        from bids and spa have
          second_price_auction_participant: "\<exists>i::participant. second_price_auction_winner n ?b x p i
                      \<and> (\<forall>j::participant. in_range n j \<and> j \<noteq> i \<longrightarrow> second_price_auction_loser n ?b x p j)"
          unfolding second_price_auction_def in_range_def by auto
        then obtain i::participant where
          i_winner: "second_price_auction_winner n ?b x p i
                      \<and> (\<forall>j::participant. in_range n j \<and> j \<noteq> i \<longrightarrow> second_price_auction_loser n ?b x p j)" 
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
    qed
  qed
  with bids show ?thesis using efficient_def_unfolded val unfolding efficient_def by blast
qed

(* unused theorems (which might nevertheless be useful for the toolbox):
   * move cursor over the word "unused_thms" for jEdit to display the list
   * This has to be at the end of the file to make sure that the whole theory has been processed. *)
unused_thms

end
