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

header {* Maximum components of vectors, and their properties *}

theory Maximum
imports Vectors
begin

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
  shows "\<exists>i::nat . i \<in> {1..n} \<and> maximum n y = y i"
    using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show "\<exists>i::nat . i \<in> {1..Suc n} \<and> maximum (Suc n) y = y i"
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
    and greater_or_equal: "\<forall>i::nat . i \<in> {1..n} \<longrightarrow> m \<ge> y i"
    and is_component: "\<exists>i::nat . i \<in> {1..n} \<and> m = y i"
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
        from False pred_non_negative maximum_is_component have "\<exists>k::nat . k \<in> {1..n} \<and> maximum n y = y k" by simp
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

(* TODO CL: discuss whether it makes sense to keep this lemma -- it's not used for "theorem vickreyA" but might still be useful for the toolbox *)
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
    have greater_or_equal: "\<forall>i::nat . i \<in> {1..n} \<longrightarrow> max' \<ge> y' i"
    by (metis linorder_not_less maximum_is_greater_or_equal order_less_trans order_refl)
  from increment have "max' = y' max_index" by simp
  (* now we have all prerequisites for applying maximum_sufficient *)
  with new_non_negative non_empty greater_or_equal index_range
    show "maximum n y' = y' max_index" using maximum_sufficient by metis
qed 

text{* We define the set of maximal components of a vector y: *}
(* TODO CL: discuss whether we should define this in a computable way.  If so, how? *)
(* TODO CL: discuss whether this function should return a set, or a vector.  How to construct such a vector?  Or should we define it as a predicate? *)
definition arg_max_set ::
  "nat \<Rightarrow> real_vector \<Rightarrow> (nat set)" where
  "arg_max_set n b = {i. i \<in> {1..n} \<and> maximum n b = b i}"

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

(* TODO CL: not sure whether we really need this, or rather just: The maximum is \<ge> the maximum of the remaining values *)
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
  from non_empty range have "\<forall>i::nat . i \<in> {1..n} \<and> i \<noteq> j \<longrightarrow> maximum_except n y j \<ge> y i" by (simp add: maximum_except_is_greater_or_equal)
  with ge_remaining have "\<forall>i::nat . i \<in> {1..n} \<and> i \<noteq> j \<longrightarrow> y j \<ge> y i" by auto
  then have greater_or_equal: "\<forall>i::nat . i \<in> {1..n} \<longrightarrow> y j \<ge> y i" by auto
  from range have is_component: "\<exists>i::nat . i \<in> {1..n} \<and> y j = y i" by auto
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
      have "\<exists>i::nat . i \<in> {1..n-(1::nat)} \<and> maximum (n-(1::nat)) (skip_index y j) = (skip_index y j) i" by simp
    then obtain i::nat where maximum_except_component: "i \<in> {1..n-(1::nat)} \<and> maximum (n-(1::nat)) (skip_index y j) = (skip_index y j) i" ..
    then have i_range: "i \<in> {1..n-(1::nat)}" ..
    from maximum_except_component maximum_except_unfolded
      have maximum_except_component_nice: "maximum_except n y j = (skip_index y j) i" by simp
    have skip_index_range: "\<dots> = y i \<or> (skip_index y j) i = y (Suc i)" unfolding skip_index_def by simp
    from i_range have 1: "i \<in> {1..n}" by auto
    from i_range have 2: "Suc i \<in> {1..n}" by auto
    from skip_index_range 1 2 have "\<exists>k::nat . k \<in> {1..n} \<and> (skip_index y j) i = y k" by auto
    (* The following (found by remote_vampire) was nearly impossible for metis to prove: *)
    (* from i_range and range and skip_index_def
      and maximum_except_component (* not sure why we need this given that we have maximum_except_component *)
      have "\<exists>k::nat . k \<in> {1..n} \<and> (skip_index y j) i = y k"
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

(* unused theorems (which might nevertheless be useful for the toolbox):
   * move cursor over the word "unused_thms" for jEdit to display the list
   * This has to be at the end of the file to make sure that the whole theory has been processed. *)
unused_thms

end

