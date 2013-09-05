(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Christoph Lange <math.semantic.web@gmail.com>
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory RelationProperties
imports Main SetUtils
begin

section {* restriction *}

text {* restriction of a relation to a set (usually resulting in a relation with a smaller domain) *}
definition restrict
(* TODO MC: compare with restr in SchorrWaite.thy
   CL@MC: doesn't seem helpful, as its type "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set" is 
   more specific than what we need. *)
:: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "||" 75)
where "R || X = X \<times> (Range R) \<inter> R"

text {* Restricting a relation to the empty set yields the empty set. *}
lemma restrict_empty: "P || {} = {}"
unfolding restrict_def by simp

text {* A restriction is a subrelation of the original relation. *}
lemma restriction_is_subrel: "P || X \<subseteq> P"
using restrict_def by blast

text {* Restricting a relation only has an effect within its domain. *}
lemma restriction_within_domain: "P || X = P || (X \<inter> (Domain P))"
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

text {* For any set, a relation equals the union of its restriction to that set and its
  pairs outside that set. *}
lemma outside_union_restrict: "P = P outside X \<union> P || X"
unfolding Outside_def restrict_def by fast

section {* evaluation as a function *}

text {* Evaluates a relation @{term R} for a single argument, as if it were a function.
  This will only work if @{term R} is a total function, i.e. if the image is always a singleton set. *}
fun eval_rel :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" (infix ",," 75) (* . (Mizar's notation) confuses Isar *)
where "eval_rel R a = the_elem (R `` {a})"

section {* right-uniqueness *}

text {* right-uniqueness of a relation (in other words: the relation is a function on its domain) *}
definition runiq :: "('a \<times> 'b) set \<Rightarrow> bool" where
(*"runiq R = (\<forall> x . R `` {x} \<subseteq> {R ,, x})"*)
"runiq R = (\<forall> x \<in> Domain R . trivial (R `` {x}))"

text {* an alternative definition of right-uniqueness in terms of @{const eval_rel} *}
lemma runiq_wrt_eval_rel:
  fixes R :: "('a \<times> 'b) set"
  shows "runiq R = (\<forall>x . R `` {x} \<subseteq> {R ,, x})"
using assms unfolding runiq_def trivial_def
by (metis (lifting) Domain_iff Image_singleton_iff eval_rel.simps subsetI)

text {* A subrelation of a right-unique relation is right-unique. *}
lemma subrel_runiq:
  fixes Q::"('a \<times> 'b) set"
    and R::"('a \<times> 'b) set"
  assumes "runiq Q"
      and "R \<subseteq> Q"
shows "runiq R"
proof -
  {
    fix a assume "a \<in> Domain R"
    then have "trivial (Q `` {a}) \<and> R `` {a} \<subseteq> (Q `` {a})" 
      using assms unfolding runiq_def trivial_def by fast
    then have "trivial (R `` {a})" using trivial_subset by (rule conjE)
  }
  then show ?thesis using runiq_def by blast
qed

text {* A singleton relation is right-unique. *}
lemma runiq_singleton_rel: "runiq {(x, y)}" (is "runiq ?R")
unfolding runiq_def
proof
  fix z assume "z \<in> Domain ?R"
  then have "z = x" by simp
  then have "?R `` {z} = {y}" by fastforce
  then show "trivial (?R `` {z})" unfolding trivial_def by (rule equalityE) simp
qed

section {* Image *}

text {* The image of a relation is only effective within the domain of that relation *}
lemma Image_within_domain: "R `` X = R `` (X \<inter> Domain R)"
by fast

text {* An alternative phrasing of @{thm Image_within_domain} *}
lemma Image_within_domain': fixes x R shows "x \<in> Domain R \<longleftrightarrow> R `` {x} \<noteq> {}"
using Image_within_domain by blast

text {* The image of a set outside a relation's domain under that domain is empty. *}
lemma Image_outside_domain:
  fixes X::"'a set"
    and R::"('a \<times> 'b) set"
shows "X \<inter> Domain R = {} \<longleftrightarrow> R `` X = {}"
using Image_within_domain by blast

section {* paste *}

text {* the union of two binary relations @{term P} and @{term Q}, where pairs from @{term Q}
  override pairs from @{term P} when their first components coincide *}
definition paste (infix "+*" 75)
where "P +* Q = (P outside Domain Q) \<union> Q"
(* Avoids possible conflicts btw P & Q using `outside', 
thus giving precedence to Q. This is particularly useful when 
P, Q are functions, and we want to preserve that property. *)

text {* If a relation @{term P} is a subrelation of another relation @{term Q} on @{term Q}'s
  domain, pasting @{term Q} on @{term P} is the same as forming their union. *}
lemma paste_subrel: assumes "P || Domain Q \<subseteq> Q" shows "P +* Q = P \<union> Q"
unfolding paste_def using assms outside_union_restrict by blast

text {* Pasting two relations with disjoint domains is the same as forming their union. *}                                                                                                
lemma paste_disj_domains: assumes "Domain P \<inter> Domain Q = {}" shows "P +* Q = P \<union> Q"
unfolding paste_def Outside_def
using assms
by fast

lemma runiq_paste1:
  fixes P::"('a \<times> 'b) set"
    and Q::"('a \<times> 'b) set"
  assumes "runiq Q"
      and "runiq (P outside Domain Q)" (is "runiq ?PoutsideQ")
  shows "runiq (P +* Q)"
proof - 
  have disjoint_domains: "Domain ?PoutsideQ \<inter> Domain Q = {}"
    using outside_reduces_domain by (metis Diff_disjoint inf_commute)
  {
    fix a assume "a \<in> Domain (?PoutsideQ \<union> Q)"
    then have triv: "trivial (?PoutsideQ `` {a}) \<and> trivial (Q `` {a})"
      using assms(1) assms(2) by (metis Image_within_domain' runiq_def trivial_empty)
    then have "?PoutsideQ `` {a} = {} \<or> Q `` {a} = {}" using disjoint_domains by blast
    then have "(?PoutsideQ \<union> Q) `` {a} = Q `` {a} \<or> (?PoutsideQ \<union> Q) `` {a} = ?PoutsideQ `` {a}" by blast
    then have "trivial ((?PoutsideQ \<union> Q) `` {a})" using triv by presburger
  }
  then have "runiq (?PoutsideQ \<union> Q)" unfolding runiq_def by blast
  then show ?thesis unfolding paste_def .
qed

corollary runiq_paste2:
  assumes "runiq Q"
      and "runiq P" 
shows "runiq (P +* Q)"
using assms runiq_paste1 subrel_runiq
by (metis Diff_subset Outside_def)

section {* Converse *}

text {* The definition of @{const converse} isn't suitable for generating code, so we provide
  a code equation using an alternative definition. *}
lemma [code_unfold]: "converse R = { (y, x) . (x, y) \<in> R }" by (rule converse_unfold)

text {* If two relations are subrelations of each other, so are their converse relations. *}
lemma converse_subrel: assumes "P \<subseteq> Q" shows "P\<inverse> \<subseteq> Q\<inverse>"
using assms by fast

(* TODO CL: check how much of the following we still need *)
section {* Christoph's old stuff *}

definition left_total_on :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool"
where "left_total_on R A \<longleftrightarrow> (\<forall> x \<in> A . \<exists> y . (x, y) \<in> R)"

definition function_on :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool"
where "function_on R A \<longleftrightarrow> left_total_on R A \<and> runiq R"

fun as_part_fun :: "('a \<times> 'b) set \<Rightarrow> 'a \<rightharpoonup> 'b"
where "as_part_fun R a = (let im = R `` {a} in 
        if card im = 1 then Some (the_elem im)
        else None)"

fun eval_rel_or :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
where "eval_rel_or R a z = (let im = R `` {a} in if card im = 1 then the_elem im else z)"

definition to_relation :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> ('a \<times> 'b) set"
where "to_relation f X = {(x, f x) | x . x \<in> X}"

definition injective :: "('a \<times> 'b) set \<Rightarrow> bool"
where "injective R \<longleftrightarrow> (\<forall> a \<in> Domain R . \<forall> b \<in> Domain R . R `` {a} = R `` {b} \<longrightarrow> a = b)"

(* TODO CL: Now that we can "easily" generate all total functions,
   maybe let's revert the "option type" stuff in nVCG.thy (which we introduced to allow for non-totality).
   Or otherwise we might enable this function to generate partial functions.
   This would have to be done by recursing not just to "xs", but to 
   all sublists of "x # xs" of length n - 1.
 *)
fun injective_functions :: "'a list \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set set"
where "injective_functions [] ys = {{}}"
    | "injective_functions (x # xs) ys = 
       \<Union> (\<lambda> f . (\<lambda> free_in_range . f \<union> {(x, free_in_range)})
                 ` (ys - (Range f)))
          ` (injective_functions xs ys)"

value "injective_functions [False,True] {0::nat, 1, 2}"

fun injective_functions_list :: "'a list \<Rightarrow> 'b\<Colon>linorder set \<Rightarrow> ('a \<times> 'b) set list"
where "injective_functions_list [] ys = [{}]"
    | "injective_functions_list (x # xs) ys = 
      concat [ map (\<lambda> free_in_range . f \<union> {(x, free_in_range)})
                 (sorted_list_of_set (ys - (Range f))) . f \<leftarrow> injective_functions_list xs ys ]"

value "injective_functions_list [False,True] {0::nat, 1, 2}"

end
