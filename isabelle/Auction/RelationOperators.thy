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
  SetUtils

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

section {* flipping pairs of relations *}

text {* flipping a pair: exchanging first and second component *}
definition flip where "flip tup = (snd tup, fst tup)"

text {* Flipped pairs can be found in the converse relation. *}
lemma flip_in_conv:
  assumes "tup \<in> R"
  shows "flip tup \<in> R\<inverse>"
using assms unfolding flip_def by simp

text {* Flipping a pair twice doesn't change it. *}
lemma flip_flip: "flip (flip tup) = tup"
by (metis flip_def fst_conv snd_conv surjective_pairing)

text {* Flipping all pairs in a relation yields the converse relation. *}
lemma flip_conv: "flip ` R = R\<inverse>"
proof -
  have "flip ` R = { flip tup | tup . tup \<in> R }" by (metis image_Collect_mem)
  also have "\<dots> = { tup . tup \<in> R\<inverse> }" using flip_in_conv by (metis converse_converse flip_flip)
  also have "\<dots> = R\<inverse>" by simp
  finally show ?thesis .
qed

text {* Summing over all pairs of a relation is the same as summing over all pairs of the
  converse relation after flipping them. *}
lemma setsum_rel_comm:
  fixes R::"('a \<times> 'b) set"
    and f::"'a \<Rightarrow> 'b \<Rightarrow> 'c\<Colon>comm_monoid_add"
  shows "(\<Sum> (x, y) \<in> R . f x y) = (\<Sum> (y', x') \<in> R\<inverse> . f x' y')"
proof -
  (* TODO CL: manually optimise some metis invocations *)
  have "inj_on flip (R\<inverse>)"
    by (metis flip_flip inj_on_def)
  moreover have "R = flip ` (R\<inverse>)"
    by (metis converse_converse flip_conv)
  moreover have "\<And> tup . tup \<in> R\<inverse> \<Longrightarrow> f (snd tup) (fst tup) = f (fst (flip tup)) (snd (flip tup))"
    by (metis flip_def fst_conv snd_conv)
  ultimately have "(\<Sum> tup \<in> R . f (fst tup) (snd tup)) = (\<Sum> tup \<in> R\<inverse> . f (snd tup) (fst tup))"
    by (rule setsum_reindex_cong)
  then show ?thesis
    by (metis (mono_tags) setsum_cong2 split_beta)
qed

section {* evaluation as a function *}

text {* Evaluates a relation @{term R} for a single argument, as if it were a function.
  This will only work if @{term R} is a total function, i.e. if the image is always a singleton set. *}
fun eval_rel :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" (infix ",," 75) (* . (Mizar's notation) confuses Isar *)
where "R ,, a = the_elem (R `` {a})"

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
(* TODO CL: report bug that structured proof found by auto sledgehammer doesn't work *)
using paste_sub_Un by blast

section {* evaluating a relation as a function *}

text {* If an input has a unique image element under a given relation, return that element; 
  otherwise return a fallback value. *}
fun eval_rel_or :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
where "eval_rel_or R a z = (let im = R `` {a} in if card im = 1 then the_elem im else z)"


notation paste (infix "+<" 75)
abbreviation singlepaste where "singlepaste F f == F +* {(fst f, snd f)}"
notation singlepaste (infix "+<" 75) (* Type of g in f +< g should avoid ambiguities *)
abbreviation prova (infix "--" 75) where "f -- x \<equiv> f outside {x}"
abbreviation ler_ni where "ler_ni r == (\<Union>x. ({x} \<times> (r x -` {True})))"
(* inverts in_rel *)
value "{(1::nat,3::nat)} +< (1,2)"


definition Graph (* compare with Function_Order.thy; 
what about Russell's antinomy, here? *)
:: "('a => 'b) => ('a \<times> 'b) set"
where "Graph f = {(x, f x) | x . True}"

definition toFunction (* inverts Graph *)
where "toFunction R = (\<lambda> x . (R ,, x))"

definition projector where "projector R =
{ (x,R``{x}) | x . 
x \<in> Domain R 
(* True *)
}
(* Graph (% x . (R `` {x}))*)
"
(* compare quotient in Equiv_Relations: here we don't require Range R and Domain R 
to have the same type.
Note that now X//R = Range (projector (R || X)), in the special case of 
R being an equivalence relation *)

definition finestpart where "finestpart X = (%x. insert x {}) ` X"
(*MC: alternative, non-computable, set-theoretical version:
Range (projector (Graph id || X)) *)

lemma ll64: shows "finestpart X = {{x}|x . x\<in>X}" using finestpart_def by auto

definition kernel where
"kernel R = (op `` (R^-1)) ` (finestpart (Range R))"

definition part2rel (*from a partition to its equivalence relation*)
:: "'a set set => ('a \<times> 'a) set"
where "part2rel X = \<Union> ((% x . (x \<times> x)) ` X)"

definition quotient where "quotient R P Q =
{(p,q)| p q. q \<in> (Range (projector Q)) & p \<in> Range (projector P) & p \<times> q \<inter> R \<noteq> {}}
(* {x \<in> Range (projector P) \<times> (Range (projector Q)) . (fst x) \<times> (snd x) \<inter> R \<noteq> {}} *)"

(*MC: to be moved to Properties *)
lemma lll40: shows "(P \<union> Q) || X = (P || X) \<union> (Q||X)" using assms restrict_def 
proof -
let ?R="P \<union> Q" have "P \<inter> (X \<times> Range ?R) = P \<inter> (X \<times> Range P)" by blast moreover have 
"Q \<inter> (X \<times> Range ?R) = Q \<inter> (X \<times> Range Q)"by fast
ultimately show ?thesis using restrict_def by (metis inf_sup_aci(1) inf_sup_distrib2)
(* MC: very slow *)
qed

definition compatible where 
-- {* Whether R takes each single P-eqclass into a subset of one single Q-eqclass.
This is usually asked when R is a function and P Q are equivalence relations 
over its domain and range, respectively.
However, such requirements are not formally needed, here. *} 
"compatible R P Q = (\<forall> x . (R``(P``{x}) \<subseteq> Q``(R``{x})))"

definition update where "update P Q = P +* (Q || (Domain P))"
(*MC: no longer used, but possibly interesting: behaves like +* (paste), but
without enlarging P's Domain. Compare with fun_upd *)
notation update (infix "+^" 75)

definition runiqer 
::"('a \<times> 'b) set => ('a \<times> 'b) set"
(* MC: A choice map to solve a multi-valued relation 
into a function of maximal domain *)
where "runiqer R={ (x, THE y. y \<in> R `` {x})| x. x \<in> Domain R }"
(* MC: alternatively: "...| x. True }" *)

definition graph where "graph X f = {(x, f x) | x. x \<in> X}" 
(* duplicates Function_Order, which is otherwise unneeded,
and I don't have enough hardware to import *)


definition ler_in where "ler_in r= (\<Union>x. ({x} \<times> (r x -` {True})))"
(* inverts in_rel *)


abbreviation "eval_rel2 (R::('a \<times> ('b set)) set) (x::'a) == \<Union> (R``{x})"
notation eval_rel2 (infix ",,," 75)
(* MC: realized that eval_rel2 could be preferable to eval_rel, because it generalizes the latter 
while evaluating to {} outside of the domain, and to something defined in general when eval_rel is not. 
This is generally a better behaviour from the formal point of view (cmp. lll74)
   CL: very nice indeed! *)
(* MC: Realized that ,,, seems to work only with set-yielding relations! 
This has to do with the fact that in HOL not everything is a set, as it happens in ZF *)


end
