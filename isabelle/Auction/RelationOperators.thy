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

theory RelationOperators
imports
  Main

begin

section {* restriction *}

text {* restriction of a relation to a set (usually resulting in a relation with a smaller domain) *}
definition restrict
(* TODO MC: compare with restr in SchorrWaite.thy
   CL@MC: doesn't seem helpful, as its type "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set" is 
   more specific than what we need. *)
:: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "||" 75)
where "R || X = X \<times> Range R \<inter> R"

text {* extensional characterisation of the pairs within a restricted relation *}
lemma restrict_ext: "R || X = {(x, y) | x y . x \<in> X \<and> (x, y) \<in> R}"
unfolding restrict_def
using Range_iff by blast
(* CL: This proof seems impossible for sledgehammer.  Range_iff is not a simp rule.  I managed
   to arrive at this point after painfully rewriting the set comprehension in very small steps,
   only to see that most of these steps could be proved by blast. *)

text {* alternative statement of @{thm restrict_ext} without explicitly naming the pair's components *}
lemma restrict_ext': "R || X = {p . fst p \<in> X \<and> p \<in> R}"
proof -
  have "R || X = {(x, y) | x y . x \<in> X \<and> (x, y) \<in> R}" by (rule restrict_ext)
  also have "\<dots> = { p . fst p \<in> X \<and> p \<in> R }" by force
  finally show ?thesis .
qed

text {* Restricting a relation to the empty set yields the empty set. *}
lemma restrict_empty: "P || {} = {}"
unfolding restrict_def by simp

text {* A restriction is a subrelation of the original relation. *}
lemma restriction_is_subrel: "P || X \<subseteq> P"
using restrict_def by blast

text {* Restricting a relation only has an effect within its domain. *}
lemma restriction_within_domain: "P || X = P || (X \<inter> (Domain P))"
unfolding restrict_def by fast

text {* alternative characterisation of the restriction of a relation to a singleton set *}
lemma restrict_to_singleton: "P || {x} = {x} \<times> P `` {x}"
unfolding restrict_def by fast

section {* relation outside some set *}

text {* For a set-theoretical relation @{term R} and an ``exclusion'' set @{term X}, return those
  tuples of @{term R} whose first component is not in @{term X}.  In other words, exclude @{term X}
  from the domain of @{term R}. *}
definition Outside :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "outside" 75) (* MC: 75 or whatever, for what I know *)
where "Outside R X = R - (X \<times> Range R)"

text {* Considering a relation outside some set @{term X} reduces its domain by @{term X}. *}
lemma outside_reduces_domain: "Domain (P outside X) = Domain P - X"
unfolding Outside_def by fast

text {* Considering a relation outside a singleton set @{term "{x}"} reduces its domain by 
  @{term x}. *}
corollary Domain_outside_singleton:
  assumes "Domain R = insert x A"
      and "x \<notin> A"
  shows "Domain (R outside {x}) = A"
using assms
using outside_reduces_domain
by (metis Diff_insert_absorb)

text {* For any set, a relation equals the union of its restriction to that set and its
  pairs outside that set. *}
lemma outside_union_restrict: "P = P outside X \<union> P || X"
unfolding Outside_def restrict_def by fast

text {* The range of a relation @{term R} outside some exclusion set @{term X} is a 
  subset of the image of the domain of @{term R}, minus @{term X}, under @{term R}. *}
lemma Range_outside_sub_Image_Domain: "Range (R outside X) \<subseteq> R `` (Domain R - X)"
using Outside_def Image_def Domain_def Range_def by blast

text {* Considering a relation outside some set doesn't enlarge its range. *}
lemma Range_outside_sub:
  assumes "Range R \<subseteq> Y"
  shows "Range (R outside X) \<subseteq> Y"
using assms
using outside_union_restrict
by (metis Range_mono inf_sup_ord(3) subset_trans)

section {* evaluation as a function *}

text {* Evaluates a relation @{term R} for a single argument, as if it were a function.
  This will only work if @{term R} is a total function, i.e. if the image is always a singleton set. *}
fun eval_rel :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" (infix ",," 75) (* . (Mizar's notation) confuses Isar *)
where "eval_rel R a = the_elem (R `` {a})"

section {* paste *}

text {* the union of two binary relations @{term P} and @{term Q}, where pairs from @{term Q}
  override pairs from @{term P} when their first components coincide *}
definition paste (infix "+*" 75)
where "P +* Q = (P outside Domain Q) \<union> Q"
(* Avoids possible conflicts btw P & Q using `outside', 
thus giving precedence to Q. This is particularly useful when 
P, Q are functions, and one wants to preserve that property. *)

text {* If a relation @{term P} is a subrelation of another relation @{term Q} on @{term Q}'s
  domain, pasting @{term Q} on @{term P} is the same as forming their union. *}
lemma paste_subrel: assumes "P || Domain Q \<subseteq> Q" shows "P +* Q = P \<union> Q"
unfolding paste_def using assms outside_union_restrict by blast

text {* Pasting two relations with disjoint domains is the same as forming their union. *}
lemma paste_disj_domains: assumes "Domain P \<inter> Domain Q = {}" shows "P +* Q = P \<union> Q"
unfolding paste_def Outside_def
using assms
by fast

text {* A relation @{term P} is equivalent to pasting its restriction to some set @{term X} on 
  @{term "P outside X"}. *}
lemma paste_outside_restrict: "P = (P outside X) +* (P || X)"
proof -
  have "Domain (P outside X) \<inter> Domain (P || X) = {}"
    unfolding Outside_def restrict_def by fast
  moreover have "P = P outside X \<union> P || X" by (rule outside_union_restrict)
  ultimately show ?thesis using paste_disj_domains by metis
qed

text {* The domain of two pasted relations equals the union of their domains. *}
lemma paste_Domain: "Domain (P +* Q) = Domain P \<union> Domain Q"
unfolding paste_def Outside_def by blast

text {* Pasting two relations yields a subrelation of their union. *}
lemma paste_sub_Un: "P +* Q \<subseteq> P \<union> Q"
unfolding paste_def Outside_def by fast

text {* The range of two pasted relations is a subset of the union of their ranges. *}
lemma paste_Range: "Range (P +* Q) \<subseteq> Range P \<union> Range Q"
using paste_sub_Un by blast

end
