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

text {* If a trivial set has a singleton subset, the latter is unique. *}
lemma singleton_sub_trivial_uniq:
  fixes x X
  assumes "{x} \<subseteq> X"
      and "trivial X"
  shows "x = the_elem X"
using assms unfolding trivial_def by fast

text {* Any subset of a trivial set is trivial. *}
lemma trivial_subset: fixes X Y assumes "trivial Y" assumes "X \<subseteq> Y" 
shows "trivial X"
using assms unfolding trivial_def by (metis (full_types) subset_empty subset_insertI2 subset_singletonD)

text {* An inference rule that combines @{thm equalityI} and @{thm subsetI} to a single step *}
lemma equalitySubsetI: "(\<And>x . x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x . x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B" by fast

text {* an equivalent notation for the image of a set, using set comprehension *}
lemma image_Collect_mem: "{ f x | x . x \<in> S } = f ` S" by auto

text {* The image of a union is the union of images. *}
lemma image_union: "f ` (X \<union> Y) = f ` X \<union> f ` Y" by auto

text {* An element is in the union of a family of sets if it is in one of the family's member sets. *}
lemma Union_member: "(\<exists> S \<in> F . x \<in> S) \<longleftrightarrow> x \<in> \<Union> F" by fast

end
