(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>


Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Locus where a function or a list (of linord type) attains its maximum value *}

theory Argmax
imports Main

begin

text {* the subset of elements of a set where a function reaches its maximum *}
fun argmax :: "('a \<Rightarrow> 'b\<Colon>linorder) \<Rightarrow> 'a set \<Rightarrow> 'a set"
where "argmax f A = { x \<in> A . f x = Max (f ` A) }"

lemma mm79: "argmax f A = A \<inter> f -` {Max (f ` A)}" by force
lemma mm86b: assumes "y \<in> f`A" shows "A \<inter> f -` {y} \<noteq> {}" using assms by blast
text {* The arg max of a function over a non-empty set is non-empty. *}
corollary argmax_non_empty_iff: assumes "finite X" "X \<noteq> {}" shows "argmax f X \<noteq>{}"
using assms Max_in finite_imageI image_is_empty mm79 mm86b by (metis(no_types))

(* MC: Yet another approach below, focusing on reusing stuff (Max, zip, map, filter) 
rather than doing our own recursion to calculate argmaxList *)

text {* We want the elements of a list satisfying a given predicate;
but, rather than returning them directly, we return the (sorted) list of their indices. 
This is done, in different ways, by @{term filterpositions} and @{term filterpositions2}.*}
definition filterpositions 
(* MC: Non(directly)recursive generalization for max_positions, have no idea about efficiency.
Given a list l, yields the indices of its elements which satisfy a given pred P*)
:: "('a => bool) => 'a list => nat list"
where "filterpositions P l = map snd (filter (P o fst) (zip l (upt 0 (size l))))"

(* MC: After some experimentations, the following, more expressive equivalent
writing also appears to be computable:*)

definition filterpositions2 
:: "('a => bool) => 'a list => nat list"
where "filterpositions2 P l = [n. n \<leftarrow> [0..<size l], P (l!n)]"

definition maxpositions :: "'a::linorder list => nat list" where
"maxpositions l = filterpositions2 (%x . x \<ge> Max (set l)) l"

lemma ll5: "maxpositions l = [n. n\<leftarrow>[0..<size l], l!n \<ge> Max(set l)]" 
using assms unfolding maxpositions_def filterpositions2_def by fastforce

definition argmaxList
:: "('a => ('b::linorder)) => 'a list => 'a list"
where "argmaxList f l = map (nth l) (maxpositions (map f l))"

lemma "[n . n <- [0..<m], (n \<in> set [0..<m] & P n)] 
= [n . n <- [0..<m], n \<in> set [0..<m], P n]" by meson

lemma ll7b: "[n . n <- l, P n] = [n . n <- l, n \<in> set l, P n]" 
proof - 
(*MC: sledgehammer-generated proof. 
I commented out the first three lines (they look quite useless), making it arguably readable. 
  assume "\<forall>v0. SMT2.fun_app uu__ v0 = (if P v0 then [v0] else [])"
  assume "\<forall>v0. SMT2.fun_app uua__ v0 = (if v0 \<in> set l then if P v0 then [v0] else [] else [])" 
  obtain v3_0 :: "('a \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> 'a" where *) 
  have "map (\<lambda>uu. if P uu then [uu] else []) l = 
    map (\<lambda>uu. if uu \<in> set l then if P uu then [uu] else [] else []) l" by simp
  thus "concat (map (\<lambda>n. if P n then [n] else []) l) = 
    concat (map (\<lambda>n. if n \<in> set l then if P n then [n] else [] else []) l)" by presburger
qed

lemma ll7: "[n . n <- [0..<m], P n] = [n . n <- [0..<m], n \<in> set [0..<m], P n]" using ll7b by fast
(* concat_map_singleton map_ident  map_ext by smt*)

lemma ll10: fixes f m P shows "(map f [n . n <- [0..<m], P n]) = [ f n . n <- [0..<m], P n]" 
by (induct m) auto

lemma map_commutes_a: "[f n . n <- [], Q (f n)] = [x <- (map f []). Q x]" by simp

lemma map_commutes_b: "\<forall> x xs. ([f n . n <- xs, Q (f n)] = [x <- (map f xs). Q x]
\<longrightarrow> [f n . n <- (x#xs), Q (f n)] = [x <- (map f (x#xs)). Q x])" using assms by simp

lemma structInduct: assumes "P []" and "\<forall>x xs. P (xs) \<longrightarrow> P (x#xs)" shows "P l" 
using assms list_nonempty_induct by (metis)

(* MC: map_commutes, filterpositions are fairly general and should be moved elsewhere *)
lemma map_commutes: fixes f::"'a => 'b" fixes Q::"'b => bool" fixes xs::"'a list" 
shows "[f n . n <- xs, Q (f n)] = [x <- (map f xs). Q x]"
using map_commutes_a map_commutes_b structInduct by fast

lemma ll9: fixes f l shows "maxpositions (map f l) =
[n . n <- [0..<size l], f (l!n) \<ge> Max (f`(set l))]" (is "maxpositions (?fl) = _")
proof -
  have "maxpositions ?fl = 
  [n. n <- [0..<size ?fl], n\<in> set[0..<size ?fl], ?fl!n \<ge> Max (set ?fl)]"
  using ll7b unfolding filterpositions2_def maxpositions_def .
  also have "... = 
  [n . n <- [0..<size l], (n<size l), (?fl!n  \<ge> Max (set ?fl))]" by simp
  also have "... = 
  [n . n <- [0..<size l], (n<size l) \<and> (f (l!n)  \<ge> Max (set ?fl))]" 
  using nth_map by (metis (poly_guards_query, hide_lams)) also have "... = 
  [n . n <- [0..<size l], (n\<in> set [0..<size l]),(f (l!n)  \<ge> Max (set ?fl))]" 
  using atLeastLessThan_iff le0 set_upt by (metis(no_types))
  also have "... =  
  [n . n <- [0..<size l], f (l!n) \<ge> Max (set ?fl)]" using ll7 by presburger 
  finally show ?thesis by auto
qed

lemma ll11: fixes f l shows "argmaxList f l = [ l!n . n <- [0..<size l], f (l!n) \<ge> Max (f`(set l))]"
unfolding ll9 argmaxList_def by (metis ll10)

theorem argmaxadequacy: 
(* MC: RHS of thesis should formally reassure about what argmaxList does.
I didn't use it directly as a definition of the latter (both appear 
to be computable) because I find filterpositions of independent interest*)
fixes f::"'a => ('b::linorder)" fixes l::"'a list" shows 
"argmaxList f l = [ x <- l. f x \<ge> Max (f`(set l))]" (is "?lh=_")
proof -
  let ?P="% y::('b::linorder) . y \<ge> Max (f`(set l))"
  let ?mh="[nth l n . n <- [0..<size l], ?P (f (nth l n))]"
  let ?rh="[ x <- (map (nth l) [0..<size l]). ?P (f x)]"
  have "?lh = ?mh" using ll11 by fast
  also have "... = ?rh" using map_commutes by fast
  also have "...= [x <- l. ?P (f x)]" using map_nth by metis
  finally show ?thesis by force
qed

end
