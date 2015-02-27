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

header {* Maximum components of vectors, and their properties *}

theory Maximum
imports Main 
(* "~~/src/HOL/Library/AList" *)
begin

text{*
The maximum component value of a vector y of non-negative values is equal to the value of one of the components, and it is greater or equal than the values of all [other] components.

We implement this as a computable function, whereas a mathematical characterization could be given by the following two axioms:
\begin{enumerate}
\item The maximum component value is equal to the value of one of the components
\item @{text maximum_is_greater_or_equal}
\end{enumerate}

Here, we derive those two statements as lemmas from the definition of the computable function.

Having the maximum as a computable function can be useful when doing concrete auctions by extracted code.
*}

subsection {* Maximum *}
text{* This subsection uses Isabelle's set maximum functions, wrapping them for our use. *}

definition maximum_defined :: "'a set \<Rightarrow> bool"
  where "maximum_defined N \<longleftrightarrow> card N > 0"

lemma maximum_except_defined:
  fixes N i
  assumes "i \<in> N" "card N > 1"
  shows "maximum_defined (N - {i})"
  unfolding maximum_defined_def
  using assms card.remove card_infinite    
  by (metis One_nat_def less_nat_zero_code neq_iff)

definition maximum :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'b"
  where "maximum N f = Max (f ` N)"

text{* If two vectors are equal, their maximum components are equal too. Note that we consider the pair consisting of an index set N and a function f as a vector. *}
lemma maximum_equal:
  fixes N :: "'a set" and f :: "'a \<Rightarrow> 'b::linorder" and g :: "'a \<Rightarrow> 'b::linorder"
  assumes "\<forall>i \<in> N. f i = g i"
  shows "maximum N f = maximum N g"
proof -
  have "f ` N = g ` N" by (rule image_cong) (auto simp: assms)
  then show ?thesis unfolding maximum_def by simp
qed

text{* The maximum component value is greater or equal than the values of all [other] components *}
lemma maximum_is_greater_or_equal:
  fixes N :: "'a set" and f :: "'a \<Rightarrow> 'b::linorder" and i :: 'a
  assumes "maximum_defined N"
    and "i \<in> N"
  shows "maximum N f \<ge> f i"
  using assms unfolding maximum_defined_def maximum_def by (simp add: card_gt_0_iff)

text{* The maximum component is one component *}
lemma maximum_is_component:
  fixes N :: "'a set" and f :: "'a \<Rightarrow> 'b::linorder"
  assumes defined: "maximum_defined N"
  shows "\<exists>i \<in> N. maximum N f = f i"
proof -
  let ?A = "f ` N"
  from defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (simp_all add: card_gt_0_iff)
  then have "Max ?A \<in> ?A" by (rule Max_in)
  then obtain i where "i \<in> N" and "Max ?A = f i" by blast
  then show ?thesis unfolding maximum_def by fast
qed

text{* Being a component of a non-negative vector and being greater or equal than all other components uniquely defines a maximum component. *}
lemma maximum_sufficient:
  fixes N :: "'a set" and f :: "'a \<Rightarrow> 'b::linorder" and m :: 'b
  assumes defined: "maximum_defined N"
    and greater_or_equal: "\<forall>i \<in> N. m \<ge> f i"
    and is_component: "\<exists>i \<in> N. m = f i"
  shows "maximum N f = m"
  unfolding maximum_def
proof -
  let ?A = "f ` N"
  show "Max ?A = m"
  proof (rule Max_eqI)
    from defined show "finite ?A"
      unfolding maximum_defined_def by (simp add: card_gt_0_iff)
    show "m \<in> ?A" using is_component by blast
    fix a assume "a \<in> ?A"
    then show "a \<le> m" using greater_or_equal by blast
  qed
qed

text{* the set of all indices of maximum components of a vector *}
definition arg_max :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a set"
  where "arg_max N f = {i \<in> N . maximum N f = f i}"
  (* need the explicit restriction "i \<in> N" as Isabelle/HOL assumes f to also be defined beyond the set N *)

text{* the set of all indices of maximum components of a vector (computable version) *}
fun arg_max_alg_list :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list"
  where "arg_max_alg_list [] f = []"
      | "arg_max_alg_list [x] f = [x]"
      | "arg_max_alg_list (x # xs) f = (let arg_max_xs = arg_max_alg_list xs f; prev_max = f (hd arg_max_xs) in
          if f x > prev_max then [x]
          else if f x = prev_max then x # arg_max_xs
          else arg_max_xs)"

text{* the set of all indices of maximum components of a vector (computable version with same signature as @{term arg_max}) *}
fun arg_max_alg :: "'a::linorder set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a set"
  where "arg_max_alg N b = set (arg_max_alg_list (sorted_list_of_set N) b)"

text{* the indices of the maximum values of the elements of a list *}
fun max_positions :: "'a::ord list \<Rightarrow> nat list" 
where "max_positions [] = []"
    | "max_positions [x] = [0]" 
    | "max_positions (x # xs) = (let 
        prevout = max_positions xs; prev_max = xs ! (hd prevout); nextout=map Suc prevout (* increment position indices *) in
        if x > prev_max then [0::nat] 
        else if x<prev_max then nextout
        else [0::nat] @ nextout (* tie case *)
    )"

fun maximum_alg_list :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'b"
  where "maximum_alg_list [] f = undefined"
      | "maximum_alg_list [x] f = f x"
      | "maximum_alg_list (x # xs) f = (let max_xs = maximum_alg_list xs f in
          if f x > max_xs then f x
          else max_xs)"

fun maximum_alg :: "'a::linorder set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'b"
  where "maximum_alg N b = maximum_alg_list (sorted_list_of_set N) b"

text{* The maximum component that remains after removing one component from a vector is greater
 or equal than the values of all remaining components *}
lemma maximum_except_is_greater_or_equal:
  fixes N :: "'a set" and f :: "'a \<Rightarrow> 'b::linorder" and j :: 'a and i :: 'a
  assumes defined: "maximum_defined N"
    and i: "i \<in> N \<and> i \<noteq> j"
  shows "maximum (N - {j}) f \<ge> f i"
proof -
  let ?M = "N - {j}"
  let ?A = "f ` ?M"
  from i have *: "i \<in> ?M" by simp
  with defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (auto simp: card_gt_0_iff)
  with * have "Max ?A \<ge> f i" by (auto simp: Max_ge_iff)
  then show ?thesis unfolding maximum_def .
qed

text{* One component of a vector is a maximum component iff it has a value greater than or equal to  the maximum of the remaining values. *}
lemma maximum_remaining_maximum:
  fixes N :: "'a set" and f :: "'a \<Rightarrow> 'b::linorder" and j :: 'a
  assumes defined': "maximum_defined (N - {j})"
    and j_max: "f j = maximum N f"
  shows "f j \<ge> maximum (N - {j}) f"
proof -
  have "f ` (N - {j}) \<subseteq> f ` N" by blast
  with defined' have "maximum (N - {j}) f \<le> maximum N f"
    unfolding maximum_def maximum_defined_def by (simp add: card_gt_0_iff Max_mono)
  also note j_max [symmetric]
  finally show ?thesis .
qed

text{* Changing one component in a vector doesn't affect the maximum of the remaining component
s. *}
lemma remaining_maximum_invariant:
  fixes N :: "'a set" and f :: "'a \<Rightarrow> 'b::linorder" and i :: 'a and a :: 'b
  shows "maximum (N - {i}) (f(i := a)) = maximum (N - {i}) f"
proof -
  let ?M = "N - {i}"
  have "f ` ?M = (f(i := a)) ` ?M" by auto
  then show ?thesis unfolding maximum_def by simp
qed

end

