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
imports SingleGoodAuction
begin

text{*
The maximum component value of a vector y of non-negative reals is equal to the value of one of the components, and it is greater or equal than the values of all [other] components.

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

definition maximum_defined :: "participant set \<Rightarrow> bool"
  where "maximum_defined N \<longleftrightarrow> card N > 0"

lemma maximum_except_defined:
  fixes N i
  assumes "i \<in> N" "card N > 1"
  shows "maximum_defined (N - {i})"
  using assms maximum_defined_def
  by (smt card.remove card_infinite)

definition maximum :: "participant set \<Rightarrow> real vector \<Rightarrow> real"
  where "maximum N y = Max (y ` N)"

text{* If two vectors are equal, their maximum components are equal too *}
lemma maximum_equal:
  fixes N :: "participant set" and y :: "real vector" and z :: "real vector"
  assumes "\<forall>i \<in> N. y i = z i"
  shows "maximum N y = maximum N z"
proof -
  have "y ` N = z ` N" by (rule image_cong) (auto simp add: assms)
  then show ?thesis unfolding maximum_def by simp
qed

text{* The maximum component value is greater or equal than the values of all [other] components *}
lemma maximum_is_greater_or_equal:
  fixes N :: "participant set" and y :: "real vector" and i :: participant
  assumes "maximum_defined N"
    and "i \<in> N"
  shows "maximum N y \<ge> y i"
  using assms unfolding maximum_defined_def maximum_def by (simp add: card_gt_0_iff)

text{* The maximum component is one component *}
lemma maximum_is_component:
  fixes N :: "participant set" and y :: "real vector"
  assumes defined: "maximum_defined N"
  shows "\<exists>i \<in> N. maximum N y = y i"
proof -
  let ?A = "y ` N"
  from defined have "finite ?A" and "?A \<noteq> {}"
    unfolding maximum_defined_def by (simp_all add: card_gt_0_iff)
  then have "Max ?A \<in> ?A" by (rule Max_in)
  then obtain i where "i \<in> N" and "Max ?A = y i" by blast
  with maximum_def show ?thesis by auto
qed

text{* Being a component of a non-negative vector and being greater or equal than all other components uniquely defines a maximum component. *}
lemma maximum_sufficient:
  fixes N :: "participant set" and y :: "real vector" and m :: real
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
definition arg_max_set :: "participant set \<Rightarrow> real vector \<Rightarrow> participant set"
  where "arg_max_set N b = {i \<in> N . maximum N b = b i}"
  (* need the explicit restriction "i \<in> N" as Isabelle assumes b to also be defined beyond the set N *)

text{* The maximum component that remains after removing one component from a vector is greater
 or equal than the values of all remaining components *}
lemma maximum_except_is_greater_or_equal:
  fixes N :: "participant set" and y :: "real vector" and j :: participant and i :: participant
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

text{* One component of a vector is a maximum component iff it has a value greater or equal tha
n the maximum of the remaining values. *}
lemma maximum_remaining_maximum:
  fixes N :: "participant set" and y :: "real vector" and j :: participant
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
  fixes N :: "participant set" and y :: "real vector" and i :: participant and a :: real
  shows "maximum (N - {i}) (y(i := a)) = maximum (N - {i}) y"
proof -
  let ?M = "N - {i}"
  have "y ` ?M = (y(i := a)) ` ?M" by auto
  then show ?thesis unfolding maximum_def by simp
qed

end

