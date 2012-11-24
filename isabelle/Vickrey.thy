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
imports SingleGoodAuction

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

section{* Maximum and related functions *}
text{*
The maximum component value of a vector y of non-negative reals is equal to the value of one of the components, and it is greater or equal than the values of all [other] components.

We implement this as a computable function, whereas in Theorema we had two axioms:
1. The maximum component value is equal to the value of one of the components
2. maximum\_is\_greater\_or\_equal

Here, we derive those two statements as lemmas from the definition of the computable function.

Having the maximum as a computable function might turn out to be useful when doing concrete auctions.
*}
fun maximum ::
  "nat \<Rightarrow> real_vector \<Rightarrow> real" where
  "maximum 0 _ = 0" | (* In our setting with non-negative real numbers it makes sense to define the maximum of the empty set as 0 *)
  "maximum (Suc n) y = max 0 (max (maximum n y) (y (Suc n)))" (* we don't enforce that y is non-negative, but this computation only makes sense for a non-negative y *)

text{* If two vectors are equal, their maximum components are equal too *}
lemma maximum_equal :
  fixes n::nat and y::real_vector and z::real_vector
  assumes "\<forall>i::nat . i \<in> {1..n} \<longrightarrow> y i = z i"
  shows "maximum n y = maximum n z"
    using assms (* Apparently this is needed; otherwise the last proof step fails. *)
(* TODO CL: Maybe restate this and other inductive statements using \<Longrightarrow> instead of assumes, as advised by Tobias Nipkow on 2012-11-22 *)
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  from Suc.prems  (* the assumptions *)
    show "maximum (Suc n) y = maximum (Suc n) z" by (simp add: Suc.hyps le_SucI)
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
  show "maximum (Suc n) y \<ge> 0" using maximum_def by simp
qed

text{* The maximum component value is greater or equal than the values of all [other] components *}
lemma maximum_is_greater_or_equal :
  fixes n::nat and y::real_vector and i::nat
  assumes "i \<in> {1..n}"
  shows "maximum n y \<ge> y i"
    using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "max (maximum n y) (y (Suc n)) \<ge> y i" (* TODO CL: ask whether there is a way of automatically decomposing the initial goal until we arrive at this expression *)
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

text{* The maximum component is one component *}
lemma maximum_is_component :
  fixes n::nat and y::real_vector
  assumes "n > 0 \<and> non_negative_real_vector n y" 
  shows "\<exists> i::nat . i \<in> {1..n} \<and> maximum n y = y i"
    using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show "\<exists> i::nat . i \<in> {1..Suc n} \<and> maximum (Suc n) y = y i"
  proof (cases "y (Suc n) \<ge> maximum n y")                                          
    case True
    from Suc.prems have "y (Suc n) \<ge> 0" unfolding non_negative_real_vector_def by simp
    with True have "y (Suc n) = maximum (Suc n) y" using maximum_def by simp
    then show ?thesis by auto (* We could directly have shown ?thesis in the previous step, but we prefer this for clarity. *)
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
    with non_empty obtain i::nat where pred_max: "i \<in> {1..n} \<and> maximum n y = y i" by (metis Suc.hyps)
    with Suc.prems have y_i_non_negative: "0 \<le> y i" unfolding non_negative_real_vector_def by simp
    have "y i = maximum n y" using pred_max by simp
    also have "\<dots> = max (maximum n y) (y (Suc n))" using False by simp
    also have "\<dots> = max 0 (max (maximum n y) (y (Suc n)))" using Suc.prems y_i_non_negative by (auto simp add: calculation min_max.le_iff_sup)
    also have "\<dots> = maximum (Suc n) y" using maximum_def non_empty by simp
    finally have max: "y i = maximum (Suc n) y" .
    with pred_max and max show ?thesis by auto
  qed
qed

text{* Being a component of a non-negative vector and being greater or equal than all other components uniquely defines a maximum component. *}
lemma maximum_sufficient :
  fixes n::nat and y::real_vector and m::real
  assumes non_negative: "non_negative_real_vector n y"
    and non_empty: "n > 0"
    and greater_or_equal: "\<forall> i::nat . i \<in> {1..n} \<longrightarrow> m \<ge> y i"
    and is_component: "\<exists> i::nat . i \<in> {1..n} \<and> m = y i"
  shows "m = maximum n y"
    using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  (* further preliminaries *)
  from Suc.prems(1) have pred_non_negative: "non_negative_real_vector n y"
    unfolding non_negative_real_vector_def by simp
  (* then go on *)
  from non_empty have max_def: "maximum (Suc n) y = max 0 (max (maximum n y) (y (Suc n)))" using maximum_def by simp
  also have "\<dots> = m"
  proof (cases "n = 0")
    case True
    with Suc.prems(4) have m_is_only_component: "m = y 1" by simp
    with Suc.prems(1) have "m \<ge> 0" unfolding non_negative_real_vector_def by simp
    (* we could break this down into further textbook-style steps, but their proofs turn out to be ugly as well, so we leave it at this high level *)
    then have "max 0 (max (maximum 0 y) (y 1)) = m" by (auto simp add: m_is_only_component)
    with True show ?thesis by simp (* this was (metis One_nat_def), but simp has access to simplification rules by default *)
  next
    case False
    show ?thesis
    proof cases
      assume last_is_max: "y (Suc n) = m"
      have "\<dots> \<ge> maximum n y"
      proof -
        from False pred_non_negative maximum_is_component have "\<exists> k::nat . k \<in> {1..n} \<and> maximum n y = y k" by simp
        then obtain k::nat where "k \<in> {1..n} \<and> maximum n y = y k" by blast
        with Suc.prems(3) show ?thesis by simp
          (* TODO CL: ask whether we should have kept using metis here.  Sledgehammer always suggests metis.
             When auto or simp also works (which is the case here, but not always), is is more efficient? *)
      qed
      then show ?thesis using last_is_max by (metis less_max_iff_disj linorder_not_le maximum_non_negative min_max.sup_absorb1 min_max.sup_commute)
    next
      assume last_is_not_max: "y (Suc n) \<noteq> m"
      (* The following doesn't work:
      with Suc.prems(4) have pred_is_component: "\<exists>k::nat . k \<in> {1..n} \<and> m = y k" by auto
      Therefore we have to use the auxiliary predicate in_range:
      *)
      from Suc.prems(4) have "\<exists>i::nat . in_range (Suc n) i \<and> m = y i" unfolding in_range_def by simp
      with last_is_not_max have "\<exists>k::nat . in_range n k \<and> m = y k" unfolding in_range_def by (metis le_antisym not_less_eq_eq)
        (* The former doesn't work when defining in_range using i \<in> {1..n}; we need the form 1 \<le> i \<and> i \<le> n *)
      then have pred_is_component: "\<exists>k::nat . k \<in> {1..n} \<and> m = y k" unfolding in_range_def by simp
      (* OK, we got what we wanted. *)
      from Suc.prems(3) have "\<forall>k::nat . k \<in> {1..n} \<longrightarrow> m \<ge> y k" by simp
      (* these, plus pred_non_negative, form the left hand side of the induction hypothesis *)
      then have "m = maximum n y" using pred_is_component pred_non_negative by (metis False Suc.hyps gr0I)
      then show ?thesis using Suc.prems(3) maximum_non_negative
        by (metis Suc(2) Suc.prems(4) maximum.simps(2) maximum_is_component maximum_is_greater_or_equal min_max.le_iff_sup min_max.sup_absorb1 zero_less_Suc)
    qed
  qed
  finally show "m = maximum (Suc n) y" .. (* ".." means: apply a canonical rule for the current context *)
qed

(* TODO CL: discuss whether it makes sense to keep this lemma – it's not used for "theorem vickreyA" but might still be useful for the toolbox *)
text{* Increasing the (actually: a) maximum component value keeps it the maximum. *}
lemma increment_keeps_maximum :
  fixes n::nat and y::real_vector and y'::real_vector and max_index::nat and max::real and max'::real
  assumes non_negative: "non_negative_real_vector n y"
    and non_empty: "n > 0"
    and index_range: "max_index \<in> {1..n}"
    and old_maximum: "maximum n y = y max_index"
    and new_lt: "y max_index < max'"
    and increment: "y' = (\<lambda> i::nat . if i = max_index then max' else y i)"
  shows "maximum n y' = y' max_index"
proof -
  from increment have new_component: "y' max_index = max'" by simp
  from non_negative index_range new_lt have "\<dots> \<ge> 0" unfolding non_negative_real_vector_def by (auto simp add: linorder_not_less order_less_trans)
  with non_negative increment have new_non_negative: "non_negative_real_vector n y'" unfolding non_negative_real_vector_def by simp
  from old_maximum new_lt increment
    have greater_or_equal: "\<forall> i::nat . i \<in> {1..n} \<longrightarrow> max' \<ge> y' i"
    by (metis linorder_not_less maximum_is_greater_or_equal order_less_trans order_refl)
  from increment have "max' = y' max_index" by simp
  (* now we have all prerequisites for applying maximum_sufficient *)
  with new_non_negative non_empty greater_or_equal index_range
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
  "arg_max_set n b \<equiv> {i. i \<in> {1..n} \<and> maximum n b = b i}"

(* for testing *)
lemma test_arg_max_set:
  shows "{1,2} \<subseteq> arg_max_set 3 (\<lambda>x. if x < 3 then 100 else 0)" (* the 1st and 2nd elements in a vector [100,100,\<dots>] are maximal. *)
apply(unfold arg_max_set_def)
apply(simp add: maximum_def)
oops (* TODO CL: This is broken since I've changed "primrec maximum" to "fun maximum" *)

text{* an alternative proof of the same lemma – still too trivial to test how declarative proofs \emph{actually} work *}
lemma test_arg_max_set_declarative:
  shows "{1,2} \<subseteq> arg_max_set 3 (\<lambda>x. if x < 3 then 100 else 0)" (* the 1st and 2nd elements in a vector [100,100,\<dots>] are maximal. *)
oops (* TODO CL: This is broken since I've changed "primrec maximum" to "fun maximum" *)
(* unfolding arg_max_set_def
  by (simp add: maximum_def) *)

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
    and range: "i \<in> {1..n}"
  shows "non_negative_real_vector (n-(1::nat)) (skip_index v i)"
proof -
  {
    fix j::nat
    assume j_range: "j \<in> {1..n-(1::nat)}"
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
  then show "non_negative_real_vector (n-(1::nat)) (skip_index v i)" unfolding non_negative_real_vector_def by simp
qed

text{* when two vectors differ in one component, skipping that component makes the vectors equal *}
lemma equal_by_skipping :
  fixes n::nat and v::real_vector and w::real_vector and j::nat and k::nat
  assumes non_empty: "n > 0"
    and j_range: "j \<in> {1..n}"
    and equal_except: "\<forall>i::nat . i \<in> {1..n} \<and> i \<noteq> j \<longrightarrow> v i = w i"
    and k_range: "k \<in> {1..n-(1::nat)}"
  shows "skip_index v j k = skip_index w j k"
proof (cases "k < j")
  case True
  then have "skip_index v j k = v k" 
    "skip_index w j k = w k"
    unfolding skip_index_def by auto
  with equal_except k_range True show ?thesis by auto
next
  case False
  then have "skip_index v j k = v (Suc k)"
   "skip_index w j k = w (Suc k)"
    unfolding skip_index_def by auto
  with equal_except k_range False show ?thesis by auto
qed

text{* We define the maximum component value that remains after removing the i-th component from the non-negative real vector y: *}
(* TODO CL: discuss whether we should demand n \<ge> 2, or whether it's fine to implicitly assume that maximum_except 1 y j is 0
   (= the "second highest bid" when there is only one bidder) *)
(* TODO CL: discuss whether we can, or should, enforce that j is \<le> n *)
(* TODO CL: ask whether there is an easier or more efficient way of stating this *)
fun maximum_except ::
  "nat \<Rightarrow> real_vector \<Rightarrow> nat \<Rightarrow> real" where
  "maximum_except 0 _ _ = 0" |
  "maximum_except (Suc n) y j =
    maximum n (skip_index y j)" (* we take y but skip its j-th component *)

(* for testing *)
value "maximum_except 3 (\<lambda> x::nat . 4-x) 1" (* the maximum component value of the vector [3,2,1], except the first element, is 2 *)

text{* The maximum component that remains after removing one component from a vector is greater or equal than the values of all remaining components *}
lemma maximum_except_is_greater_or_equal :
  fixes n::nat and y::real_vector and j::nat and i::nat
  assumes j_range: "n \<ge> 1 \<and> j \<in> {1..n}"
    and i_range: "i \<in> {1..n} \<and> i \<noteq> j"
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
    from True j_range i_range pred_n have "i \<in> {1..pred_n}" by simp
    then have "maximum pred_n ?y_with_j_skipped \<ge> ?y_with_j_skipped i" by (simp add: maximum_is_greater_or_equal)
    with can_skip_j pred_n show ?thesis by simp
  next
    case False
    with i_range have case_False_nice: "i > j" by simp
    then obtain pred_i where pred_i: "i = Suc pred_i" by (rule lessE) (* TODO CL: ask why this works.  I do not really understand what lessE does. *)
    from case_False_nice pred_i (* wouldn't work with "from False" *)
      have can_skip_j_and_shift_left: "y i = ?y_with_j_skipped pred_i" unfolding skip_index_def by simp
    from case_False_nice i_range j_range pred_i pred_n
      have (* actually 2 \<le> i, but we don't need this *) "pred_i \<in> {1..pred_n}" by simp
    then have "maximum pred_n ?y_with_j_skipped \<ge> ?y_with_j_skipped pred_i" by (simp add: maximum_is_greater_or_equal)
    with can_skip_j_and_shift_left pred_n show ?thesis by simp
  qed
qed

text{* One component of a vector is a maximum component iff it has a value greater or equal than the maximum of the remaining values. *}
lemma maximum_greater_or_equal_remaining_maximum :
  (* TODO CL: discuss the name of this lemma; maybe there is something more appropriate *)
  fixes n::nat and y::real_vector and j::nat
  assumes non_negative: "non_negative_real_vector n y"
    and non_empty: "n > 0"
    and range: "j \<in> {1..n}"
  shows "y j \<ge> maximum_except n y j \<longleftrightarrow> y j = maximum n y"
proof
  assume ge_remaining: "y j \<ge> maximum_except n y j"
  from non_empty range have "\<forall> i::nat . i \<in> {1..n} \<and> i \<noteq> j \<longrightarrow> maximum_except n y j \<ge> y i" by (simp add: maximum_except_is_greater_or_equal)
  with ge_remaining have "\<forall> i::nat . i \<in> {1..n} \<and> i \<noteq> j \<longrightarrow> y j \<ge> y i" by auto
  then have greater_or_equal: "\<forall> i::nat . i \<in> {1..n} \<longrightarrow> y j \<ge> y i" by auto
  from range have is_component: "\<exists> i::nat . i \<in> {1..n} \<and> y j = y i" by auto
    (* when we first tried non_empty: "n \<ge> 1" sledgehammer didn't find a proof for this *)
  with non_negative non_empty greater_or_equal show "y j = maximum n y" by (simp add: maximum_sufficient)
  (* TODO CL: ask whether it makes a difference to use "by auto" vs. "by simp" (or even "by simp") when either would work,
              and what's the difference between "from foo show bar by simp" vs. "show bar by (simp add: foo)" *)
next (* nice to see that support for \<longleftrightarrow> is built in *)
  assume j_max: "y j = maximum n y"
  from non_empty
    have maximum_except_unfolded: "maximum_except n y j = maximum (n-(1::nat)) (skip_index y j)"
    by (metis Suc_diff_1 maximum_except.simps(2))
  show "y j \<ge> maximum_except n y j"
  proof (cases "n = 1")
    case True
    with maximum_except_unfolded maximum_def have "maximum_except n y j = 0" by simp
    with j_max non_negative show ?thesis by (simp add: maximum_non_negative)
  next
    case False
    from j_max have ge: "\<forall>k::nat . k \<in> {1..n} \<longrightarrow> y j \<ge> y k" by (simp add: maximum_is_greater_or_equal)
    from False non_empty have "n > 1" by simp
    then have pred_non_empty: "(n-(1::nat)) > 0" by simp
    from non_empty non_negative range have pred_non_negative: "non_negative_real_vector (n-(1::nat)) (skip_index y j)"
      by (metis skip_index_keeps_non_negativity)
    from pred_non_empty pred_non_negative maximum_is_component
      have "\<exists> i::nat . i \<in> {1..n-(1::nat)} \<and> maximum (n-(1::nat)) (skip_index y j) = (skip_index y j) i" by simp
    then obtain i::nat where maximum_except_component: "i \<in> {1..n-(1::nat)} \<and> maximum (n-(1::nat)) (skip_index y j) = (skip_index y j) i" ..
    then have i_range: "i \<in> {1..n-(1::nat)}" ..
    from maximum_except_component maximum_except_unfolded
      have maximum_except_component_nice: "maximum_except n y j = (skip_index y j) i" by simp
    have skip_index_range: "\<dots> = y i \<or> (skip_index y j) i = y (Suc i)" unfolding skip_index_def by simp
    from i_range have 1: "i \<in> {1..n}" by auto
    from i_range have 2: "Suc i \<in> {1..n}" by auto
    from skip_index_range 1 2 have "\<exists> k::nat . k \<in> {1..n} \<and> (skip_index y j) i = y k" by auto
    (* The following (found by remote_vampire) was nearly impossible for metis to prove: *)
    (* from i_range and range and skip_index_def
      and maximum_except_component (* not sure why we need this given that we have maximum_except_component *)
      have "\<exists> k::nat . k \<in> {1..n} \<and> (skip_index y j) i = y k"
      by (metis (full_types) One_nat_def Suc_neq_Zero Suc_pred' leD less_Suc0 less_Suc_eq_le linorder_le_less_linear) *)
    then obtain k::nat where "k \<in> {1..n} \<and> (skip_index y j) i = y k" ..
    with ge maximum_except_component_nice show "y j \<ge> maximum_except n y j" by simp
  qed
qed

text{* Changing one component in a vector doesn't affect the maximum of the remaining components. *}
lemma remaining_maximum_invariant :
  (* TODO CL: discuss the name of this lemma; maybe there is something more appropriate *)
  fixes n::nat and y::real_vector and i::nat and a::real
  assumes non_empty: "n > 0" and
    range: "i \<in> {1..n}"
  shows "maximum_except n y i = maximum_except n (deviation n y a i) i"
proof -
  from range have equal_except: "\<forall>j::nat . j \<in> {1..n} \<and> j \<noteq> i \<longrightarrow> y j = deviation n y a i j"
    unfolding deviation_def by simp
  with non_empty range
    have "\<forall>k::nat . k \<in> {1..n-(1::nat)} \<longrightarrow> skip_index y i k = skip_index (deviation n y a i) i k"
    using equal_by_skipping by (auto simp add: deviation_def)
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
