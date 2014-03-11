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
  have "trivial X" sorry (* prove *)
  then have "Q X"
  proof (cases rule: trivial_cases)
    case empty
    then show ?thesis sorry (* prove *)
  next
    case (singleton x)
    then show ?thesis sorry (* prove *)
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

text {* If there exists a unique @{term x} with some property, then the set 
  of all such @{term x} is trivial. *}
lemma ex1_imp_trivial:
  assumes "\<exists>! x . P x"
  shows "trivial { x . P x }"
proof -
  from assms have "\<forall> a b . a \<in> { x . P x } \<and> b \<in> { x . P x } \<longrightarrow> a = b" by blast
  then show ?thesis by (rule no_distinct_imp_trivial)
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

section {* Set difference *}

(*
A = {1,2}
B = {1,3}
A = B - {3} \<union> {2}
*)

(* TODO CL: document *)
lemma Diff_replace:
  assumes A_repl_B: "A = B - {x} \<union> {y}"
      and card_eq: "card B = card A"
      and old_elem: "x \<in> B"
  shows "A - B = {y} - {x}"
(* TODO CL: In Isabelle2013-1-RC3, this is hard for Sledgehammer to find.
   Maybe optimise manually. *)
proof cases
  assume "x = y"
  then show ?thesis
    by (metis A_repl_B Diff_cancel Un_insert_right insert_Diff_single insert_absorb old_elem sup_bot_right)
next
  assume "x \<noteq> y"
  with A_repl_B have "A - A \<inter> B = {y}" sorry
oops
(*
This was the proof when when we had assumed B \<subseteq> A, which we are actually not interested in:
using assms
by (metis Diff_cancel Diff_insert_absorb Un_empty_right Un_insert_right insert_iff Set.set_insert set_rev_mp)
*)

text {* Subtracting a proper subset from a set yields another proper subset. *}
lemma Diff_psubset_is_psubset:
  assumes "A \<noteq> {}"
      and "A \<subset> B"
  shows "B - A \<subset> B"
(* TODO CL: maybe report to Isabelle mailing list: "try" without "using assms" finds a lengthy 
   Sledgehammer proof, so maybe the obvious "using assms" should always be tried first? *)
using assms
by blast

section {* Big Union *}

text {* An element is in the union of a family of sets if it is in one of the family's member sets. *}
lemma Union_member: "(\<exists> S \<in> F . x \<in> S) \<longleftrightarrow> x \<in> \<Union> F" by blast

lemma Union_map_member:
  assumes "x \<in> \<Union> { f y | y . y \<in> Z }"
  shows "\<exists> y \<in> Z . x \<in> f y"
using assms by fast

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

(* TODO CL: find better name *)
lemma Union_map_compr_eq1:
  fixes x::'a
    and f::"'b \<Rightarrow> 'a set"
    and P::"'b set"
  shows "x \<in> (\<Union> {f Y | Y . Y \<in> P}) \<longleftrightarrow> (\<exists> Y \<in> P . x \<in> f Y)"
(* CL: the following proof takes 2.64s in Isabelle2013-1-RC1:
   by (metis UN_iff Union_set_compr_eq) *)
proof -
  have "x \<in> (\<Union> {f Y | Y . Y \<in> P}) \<longleftrightarrow> x \<in> (\<Union> (f ` P))" by (simp add: image_Collect_mem)
  also have "\<dots> \<longleftrightarrow> (\<exists> y \<in> (f ` P) . x \<in> y)" by (rule Union_iff)
  also have "\<dots> \<longleftrightarrow> (\<exists> y . y \<in> (f ` P) & x \<in> y)" by force
  also have "\<dots> \<longleftrightarrow> (\<exists> y \<in> (f ` P) . x \<in> y)" by blast
  also have "\<dots> \<longleftrightarrow> (\<exists> Y \<in> P . x \<in> (f Y))" by force
  finally show ?thesis .
qed

text {* Growing, in terms of set union a member @{term x} of a family of sets by a set @{term x'} grows
  the union of all of these sets by @{term x'}. *}
lemma Union_family_grown_member:
  fixes Q::"'a set set"
    and P::"'a set set"
    and A::"'a set"
    and x::"'a set"
    and x'::"'a set"
  assumes grow_member: "Q = P - {x} \<union> {x' \<union> x}"
      and Union_before: "\<Union> P = A - x'"
      and increment_sub_set: "x' \<subseteq> A"
      and old_member_in_family: "x \<in> P"
  shows "\<Union> Q = A"
(* CL: This proof was found by Sledgehammer and cleaned up manually, but it may need further cleanups. *)
(*
Sledgehammer once found this alternative (something like 104 ms in Isabelle2013-1-RC3) but now can't find it any more:
by (smt Sup_insert Un_Diff_cancel Un_assoc Un_commute insert_absorb insert_def singleton_conv subset_Un_eq)
*)
using assms
proof -
  obtain remove :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
    where remove_def: "\<forall>y S. y \<in> S \<longrightarrow> insert y (remove y S) = S \<and> y \<notin> remove y S"
    using [[metis_new_skolem]] by (metis Set.set_insert)
  have f2: "\<forall>B C D. \<not> B \<union> C \<subseteq> D \<or> D \<union> C = D"
    by auto
  have f3: "\<forall>y S. \<Union>insert y S = \<Union>S \<union> y"
    by auto (* TODO CL: make this a lemma of its own *)

  have f4: "\<Union>insert x' P = A"
    using Union_before increment_sub_set by force
  then have f5: "\<forall>y. \<Union>insert y (insert x' P) = A \<union> y"
    by auto

  have f9: "insert (x \<union> x') (P - {x}) = Q"
    using grow_member by auto
  then have "\<forall>y . y \<in> Q \<or> x \<union> x' \<noteq> y"
    by fastforce
  then have "x \<union> x' \<subseteq> \<Union>Q"
    by (metis Sup_upper)
  then have f13: "\<Union>Q = \<Union>insert x Q"
    using Union_insert by force

  have f12: "insert (x \<union> x') (remove x P) = Q"
    using remove_def f9 old_member_in_family by (metis Diff_insert_absorb)

  have "x \<subseteq> A"
    using f4 old_member_in_family by auto
  moreover have "\<forall>y. \<not> y \<subseteq> A \<or> y \<union> x' \<subseteq> A"
    using increment_sub_set by simp
  ultimately have "x \<union> x' \<subseteq> A"
    by blast
  moreover have "\<forall>y. \<Union>insert x' (insert y P) = A \<union> y"
    using f5 by auto
  moreover have "insert x Q = insert (x \<union> x') P"
    using remove_def f12 old_member_in_family by (metis insert_commute)
  ultimately have "\<Union>insert x' (insert x Q) = A"
    by (metis Un_absorb2)
  moreover have "\<forall>y y'. x \<union> x' \<noteq> y \<or> y \<in> insert y' Q"
    using f9 by fastforce
  ultimately have "\<Union>insert x Q = A"
    using f2 f3 by (metis Sup_upper)
  then show ?thesis
    using f13 by fastforce
qed

section {* Miscellaneous *}

text {* A set comprehension formed over a property, which is satisfied by exactly 
  one object, yields a singleton set containing that object. *}
lemma Collect_uniq_prop_singleton:
  assumes "\<exists>! x . P x"
  shows "{ x . P x } = { THE x . P x }"
using assms
(* TODO CL: optimise by some manual steps *)
by (metis (full_types) Collect_cong singleton_conv2 theI')

lemma ll69: assumes "trivial t" "t \<inter> X \<noteq> {}" shows "t \<subseteq> X" using trivial_def assms 
by (smt disjoint_iff_not_equal in_mono singleton_iff subsetI)

lemma ll97: assumes "finite X" shows "trivial X=(card X \<le> 1)" (is "?LH=?RH") using trivial_def assms 
proof -
  {
    assume "card X=1" 
    hence "X = {the_elem X}" 
    using assms the_elem_def card_def by (smt card_eq_SucD the_elem_eq)
    hence "?LH" using trivial_def by auto
  }
  also have "card X=0 \<longrightarrow> X={} \<longrightarrow> ?LH" using trivial_def by fast
  hence "card X=0 \<longrightarrow> ?LH" by (metis assms card_eq_0_iff)
  ultimately have "?RH \<longrightarrow> ?LH" by linarith
  also have "?LH \<longrightarrow> ?RH" using trivial_def assms 
  by (smt bot_set_def card.insert card_empty card_gt_0_iff card_mono empty_def equals0D finite.emptyI finite.insertI finite.simps insert_absorb insert_not_empty)
  ultimately show ?thesis by fast
qed

lemma ll10: shows "trivial {x}" by (metis order_refl the_elem_eq trivial_def)

lemma ll11: assumes "trivial X" "{x} \<subseteq> X" shows "{x}=X" 
using singleton_sub_trivial_uniq assms by (metis subset_antisym trivial_def)

lemma ll26: assumes "\<not> trivial X" "trivial T" shows "X-T \<noteq> {}"
using assms by (metis Diff_iff empty_iff subsetI trivial_subset)

lemma ll40: assumes "trivial X" "trivial Y" shows "trivial (X \<times> Y)"
proof -
let ?e=the_elem let ?x="?e X" let ?y="?e Y" let ?Z="X \<times> Y"
have "X \<subseteq> {?x} & Y \<subseteq> {?y}" using assms trivial_def by metis
hence "?Z \<subseteq> {(?x,?y)}" by blast
thus ?thesis using trivial_subset trivial_singleton by metis
qed

end
