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

text {* restriction of a relation to a set (usually resulting in a relation with a smaller domain) *}
definition restrict
(* TODO MC: compare with restr in SchorrWaite.thy
   CL@MC: doesn't seem helpful, as its type "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set" is 
   more specific than what we need. *)
:: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "||" 75)
where "R || X = X \<times> (Range R) \<inter> R"

text {* For a set-theoretical relation @{term R} and an ``exclusion'' set @{term X}, return those
  tuples of @{term R} whose first component is not in @{term X}.  In other words, exclude @{term X}
  from the domain of @{term R}. *}
definition Outside :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "outside" 75) (* MC: 75 or whatever, for what I know *)
where "Outside R X = R - (X \<times> Range R)"

text {* Considering a relation outside some set @{term X} reduces its domain by @{term X}. *}
lemma outside_reduces_domain: "Domain (P outside X) = Domain P - X"
unfolding Outside_def by fast

text {* Evaluates a relation @{term R} for a single argument, as if it were a function.
  This will only work if @{term R} is a total function, i.e. if the image is always a singleton set. *}
fun eval_rel :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" (infix ",," 75) (* . (Mizar's notation) confuses Isar *)
where "eval_rel R a = the_elem (R `` {a})"

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

definition inverse :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'a) set"
where "inverse R = { (y, x) . (x, y) \<in> R }"

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
