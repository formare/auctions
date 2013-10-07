(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati <marco.caminati@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Additional material that we would have expected in Set.thy *}

theory SetUtils
imports
  Main

begin

section {* Equality *}

text {* An inference rule that combines @{thm equalityI} and @{thm subsetI} to a single step *}
lemma equalitySubsetI: "(\<And>x . x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x . x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B" by blast

section {* Trivial sets *}

text {* A trivial set (i.e. singleton or empty), as in Mizar *}
definition trivial where "trivial x = (x \<subseteq> {the_elem x})"

text {* The empty set is trivial. *}
lemma trivial_empty: "trivial {}" unfolding trivial_def by (rule empty_subsetI)

text {* A singleton set is trivial. *}
lemma trivial_singleton: "trivial {x}" unfolding trivial_def by simp

text {* Infrastructure for proving some property of a trivial set by distinguishing the 
  two cases @{text empty} and @{text "singleton x"}. *}
(* CL: thanks to Christian Sternagel and Joachim Breitner
http://stackoverflow.com/questions/18686865/how-can-i-bind-the-schematic-variable-case-in-a-rule-for-proof-by-cases
By "cases pred: trivial" one could enable this rule by default; this would also allow to omit "consumes 1". *)
lemma trivial_cases [case_names empty singleton, consumes 1]:
  assumes "trivial X"
  assumes empty: "X = {} \<Longrightarrow> P"
      and singleton: "\<And> x . X = {x} \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: trivial_def)

(* How to use trivial_cases:
notepad
begin
  fix Q
  fix X::"'a set"
  have "trivial X" sorry
  then have "Q X"
  proof (cases rule: trivial_cases)
    case empty
    then show ?thesis sorry
  next
    case (singleton x)
    then show ?thesis sorry
  qed
end
*)

text {* There are no two different elements in a trivial set. *}
lemma trivial_imp_no_distinct:
  assumes triv: "trivial X"
      and x: "x \<in> X"
      and y: "y \<in> X"
  shows "x = y"
(* CL: The following takes 17 ms in Isabelle2013-1-RC1:
   by (metis equals0D insertE triv trivial_cases x y) *)
proof -
  from triv show "x = y"
  proof (cases rule: trivial_cases)
    case empty
    with x show ?thesis by simp
  next
    case singleton
    with x y show ?thesis by fast
  qed
qed

text {* If there are no two different elements in a set, it is trivial. *}
lemma no_distinct_imp_trivial:
  assumes "\<forall> x y . x \<in> X \<and> y \<in> X \<longrightarrow> x = y"
  shows "trivial X"
(* CL: The following takes 81 ms in Isabelle2013-1-RC1:
   by (metis assms ex_in_conv insertI1 subsetI subset_singletonD trivial_def trivial_singleton) *)
unfolding trivial_def
proof 
  fix x::'a
  assume x_in_X: "x \<in> X"
  with assms have uniq: "\<forall> y \<in> X . x = y" by force
  have "X = {x}"
  proof (rule equalitySubsetI)
    fix x'::'a
    assume "x' \<in> X"
    with uniq show "x' \<in> {x}" by simp
  next
    fix x'::'a
    assume "x' \<in> {x}"
    with x_in_X show "x' \<in> X" by simp
  qed
  then show "x \<in> {the_elem X}" by simp
qed

text {* If a trivial set has a singleton subset, the latter is unique. *}
lemma singleton_sub_trivial_uniq:
  fixes x X
  assumes "{x} \<subseteq> X"
      and "trivial X"
  shows "x = the_elem X"
(* CL: The following takes 16 ms in Isabelle2013-1-RC1:
   by (metis assms(1) assms(2) insert_not_empty insert_subset subset_empty subset_insert trivial_def trivial_imp_no_distinct) *)
using assms unfolding trivial_def by fast

text {* Any subset of a trivial set is trivial. *}
lemma trivial_subset: fixes X Y assumes "trivial Y" assumes "X \<subseteq> Y" 
shows "trivial X"
(* CL: The following takes 36 ms in Isabelle2013-1-RC1:
   by (metis assms(1) assms(2) equals0D no_distinct_imp_trivial subsetI subset_antisym subset_singletonD trivial_cases) *)
using assms unfolding trivial_def by (metis (full_types) subset_empty subset_insertI2 subset_singletonD)

section {* The image of a set under a function *}

(* TODO CL: review whether we are always using the simplest possible set comprehension notation (compare List.set_concat) *)
text {* an equivalent notation for the image of a set, using set comprehension *}
lemma image_Collect_mem: "{ f x | x . x \<in> S } = f ` S" by auto

section {* Miscellaneous *}

text {* An element is in the union of a family of sets if it is in one of the family's member sets. *}
lemma Union_member: "(\<exists> S \<in> F . x \<in> S) \<longleftrightarrow> x \<in> \<Union> F" by blast

lemma Union_map_member:
  assumes "x \<in> \<Union> { f y | y . y \<in> Z }"
  shows "\<exists> y \<in> Z . x \<in> f y"
using assms
by (auto simp: UnionE)

text {* When a set of elements @{term A} is non-empty, and a function @{term f} returns a non-empty
  set for at least one member of @{term A}, the union of the image of @{term A} under @{term f}
  is non-empty, too. *}
lemma Union_map_non_empty:
  assumes "x \<in> A"
      and "f x \<noteq> {}"
  shows "\<Union> (f ` A) \<noteq> {}"
proof -
  from assms(1) have "f ` A \<noteq> {}" by fast
  with assms show ?thesis by force
qed

text {* Two alternative notations for the big union operator involving set comprehension are
  equivalent. *}
lemma Union_set_compr_eq: "(\<Union> x\<in>A . f x) = \<Union> { f x | x . x \<in> A }"
proof (rule equalitySubsetI)
  fix y
  assume "y \<in> (\<Union> x\<in>A . f x)"
  then obtain z where "z \<in> { f x | x . x \<in> A }" and "y \<in> z" by blast
  then show "y \<in> \<Union> { f x | x . x \<in> A }" by (rule UnionI)
next
  fix y
  assume "y \<in> \<Union> { f x | x . x \<in> A }"
  then show "y \<in> (\<Union> x\<in>A . f x)" by force
qed

end
