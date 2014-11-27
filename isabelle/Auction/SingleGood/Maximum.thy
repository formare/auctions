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

We implement this as a computable function, whereas in Theorema we had two axioms:
\begin{enumerate}
\item The maximum component value is equal to the value of one of the components
\item @{text maximum_is_greater_or_equal}
\end{enumerate}

Here, we derive those two statements as lemmas from the definition of the computable function.

Having the maximum as a computable function might turn out to be useful when doing concrete auctions.
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
  where "maximum N y = Max (y ` N)"

text{* If two vectors are equal, their maximum components are equal too *}
lemma maximum_equal:
  fixes N :: "'a set" and y :: "'a \<Rightarrow> 'b::linorder" and z :: "'a \<Rightarrow> 'b::linorder"
  assumes "\<forall>i \<in> N. y i = z i"
  shows "maximum N y = maximum N z"
proof -
  have "y ` N = z ` N" by (rule image_cong) (auto simp: assms)
  then show ?thesis unfolding maximum_def by simp
qed

text{* The maximum component value is greater or equal than the values of all [other] components *}
lemma maximum_is_greater_or_equal:
  fixes N :: "'a set" and y :: "'a \<Rightarrow> 'b::linorder" and i :: 'a
  assumes "maximum_defined N"
    and "i \<in> N"
  shows "maximum N y \<ge> y i"
  using assms unfolding maximum_defined_def maximum_def by (simp add: card_gt_0_iff)

text{* The maximum component is one component *}
lemma maximum_is_component:
  fixes N :: "'a set" and y :: "'a \<Rightarrow> 'b::linorder"
  assumes defined: "maximum_defined N"
  shows "\<exists>i \<in> N. maximum N y = y i"
proof -
  let ?A = "y ` N"
  from defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (simp_all add: card_gt_0_iff)
  then have "Max ?A \<in> ?A" by (rule Max_in)
  then obtain i where "i \<in> N" and "Max ?A = y i" by blast
  then show ?thesis unfolding maximum_def by fast
qed

text{* Being a component of a non-negative vector and being greater or equal than all other components uniquely defines a maximum component. *}
lemma maximum_sufficient:
  fixes N :: "'a set" and y :: "'a \<Rightarrow> 'b::linorder" and m :: 'b
  assumes defined: "maximum_defined N"
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
    show "m \<in> ?A" using is_component by blast
    fix a assume "a \<in> ?A"
    then show "a \<le> m" using greater_or_equal by blast
  qed
qed

text{* the set of all indices of maximum components of a vector *}
definition arg_max :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a set"
  where "arg_max N b = {i \<in> N . maximum N b = b i}"
  (* need the explicit restriction "i \<in> N" as Isabelle/HOL assumes b to also be defined beyond the set N *)

text{* the set of all indices of maximum components of a vector (computable version) *}
fun arg_max_alg_list :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list"
  where "arg_max_alg_list [] f = []"
      | "arg_max_alg_list [x] f = [x]"
      | "arg_max_alg_list (x # xs) f = (let arg_max_xs = arg_max_alg_list xs f; prev_max = f (hd arg_max_xs) in
          if f x > prev_max then [x]
          else if f x = prev_max then x # arg_max_xs
          else arg_max_xs)"
(* concerning information entropy it may be stupid to apply this "arg max" to an index set [31,45,99]
   because the same set could be represented as [0,1,2], and then we could implement the whole function
   in a different way: not finding the domain elements at which a function reaches its maximum value,
   but finding the indices of the maximum elements of a list (which is indexed 0,1,2,\<dots>).  The latter is realised
   by the max_positions function below.

   However, in the setting where this function will be applied, this doesn't make much of a difference.
   In an auction with 100 participants all we need to do is to number them in an economic way as 0,\<dots>,99,
   and then the winner determination and payment computation will end up calling arg_max with index sets
   [1,\<dots>,99], [0,2,\<dots>,99], [0,1,3,\<dots>,99], \<dots>
*)

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
  where "maximum_alg_list [] b = undefined" (* TODO CL: throw exception as per https://github.com/formare/auctions/issues/17 *)
      | "maximum_alg_list [x] b = b x"
      | "maximum_alg_list (x # xs) b = (let max_xs = maximum_alg_list xs b in
          if b x > max_xs then b x
          else max_xs)"

fun maximum_alg :: "'a::linorder set \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'b"
  where "maximum_alg N b = maximum_alg_list (sorted_list_of_set N) b"

text{* The maximum component that remains after removing one component from a vector is greater
 or equal than the values of all remaining components *}
lemma maximum_except_is_greater_or_equal:
  fixes N :: "'a set" and y :: "'a \<Rightarrow> 'b::linorder" and j :: 'a and i :: 'a
  assumes defined: "maximum_defined N"
    and i: "i \<in> N \<and> i \<noteq> j"
  shows "maximum (N - {j}) y \<ge> y i"
proof -
  let ?M = "N - {j}"
  let ?A = "y ` ?M"
  from i have *: "i \<in> ?M" by simp
  with defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (auto simp: card_gt_0_iff)
  with * have "Max ?A \<ge> y i" by (auto simp: Max_ge_iff)
  then show ?thesis unfolding maximum_def .
qed

text{* One component of a vector is a maximum component iff it has a value greater or equal tha
n the maximum of the remaining values. *}
lemma maximum_remaining_maximum:
  fixes N :: "'a set" and y :: "'a \<Rightarrow> 'b::linorder" and j :: 'a
  assumes defined': "maximum_defined (N - {j})"
    and j_max: "y j = maximum N y"
  shows "y j \<ge> maximum (N - {j}) y"
proof -
  have "y ` (N - {j}) \<subseteq> y ` N" by blast
  with defined' have "maximum (N - {j}) y \<le> maximum N y"
    unfolding maximum_def maximum_defined_def by (simp add: card_gt_0_iff Max_mono)
  also note j_max [symmetric]
  finally show ?thesis .
qed

text{* Changing one component in a vector doesn't affect the maximum of the remaining component
s. *}
lemma remaining_maximum_invariant:
  fixes N :: "'a set" and y :: "'a \<Rightarrow> 'b::linorder" and i :: 'a and a :: 'b
  shows "maximum (N - {i}) (y(i := a)) = maximum (N - {i}) y"
proof -
  let ?M = "N - {i}"
  have "y ` ?M = (y(i := a)) ` ?M" by auto
  then show ?thesis unfolding maximum_def by simp
qed

(* TODO CL: revise as per https://github.com/formare/auctions/issues/17 *)

(* TODO CL: re-enable this (but it's not used anyway) once we have a more efficient proof.
   With Isabelle2013-1-RC1 this one takes ages.
lemma ll2: fixes l shows "zip l (upt 0 (size l))= [(l!n,n). n \<leftarrow> [0..<size l]]" 
using assms zip_def upt_def 
by (smt length_map length_zip list_eq_iff_nth_eq map_nth nth_map nth_zip)*)

(*lemma mk01: "[ x <- l. f x \<ge> Max (f`(set l))] = [ x <- l. f x = Max (f`(set l))]" using  
List.finite_set Max.coboundedI eq_iff finite_imageI image_eqI filter_cong
(* by smt2 *)

corollary "set (argmaxList f l) = argmax f (set l)" 
using assms argmaxadequacy mk01 by (metis (full_types) argmax.elims set_filter)  
*)

end

