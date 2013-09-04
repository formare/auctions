(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory a
(*MC@CL: I was thinking about moving everything here into RelationProperties, OK?

CL: Makes sense, almost.  I moved "trivial" to SetUtils, as it is not about _relations_.

Once touching RelationProperties keep in mind that it may contain some code
that is redundant with what you have in a.thy and b.thy.  Such as my old computation of 
injective functions.  Some of this may be obsolete now, or it may be worth preserving in 
an "alternative" section; compare Partitions.
*)
imports  Equiv_Relations SetUtils RelationProperties Partitions SEQ
(*"$AFP/Collections/common/Misc"*)

begin

definition runiq where (*whether a relation is a function*)
(*"runiq R = (\<forall> x . R `` {x} \<subseteq> {R ,, x})"*)
"runiq R = (\<forall> X . trivial X \<longrightarrow> trivial (R `` X))"
definition restrict (* compare with restr in SchorrWaite.thy *)
:: "('a \<times> 'b) set => 'a set => ('a \<times> 'b) set "
where "restrict R X = X \<times> (Range R) \<inter> R"

text {* For a set-theoretical relation @{term R} and an ``exclusion'' set @{term X}, return those
  tuples of @{term R} whose first component is not in @{term X}.  In other words, exclude @{term X}
  from the domain of @{term R}. *}
definition Outside 
where "Outside R X = R - (X \<times> Range R)"
notation Outside (infix "outside" 75) (* MC: 75 or whatever, for what I know *)

notation restrict (infix "||" 75)
notation eval_rel (infix ",," 75) (* . (Mizar's notation) confuses Isar *)
definition paste where "paste P Q = (P outside Domain Q) \<union> Q"
(* Avoids possible conflicts btw P & Q using `outside', 
thus giving precedence to Q. This is particularly useful when 
P, Q are functions, and we want to preserve that property. *)
notation paste (infix "+*" 75)
definition Graph (* compare with Function_Order.thy; 
what about Russell's antinomy, here? *)
:: "('a => 'b) => ('a \<times> 'b) set"
where "Graph f = {(x, f x) | x . True}"
definition toFunction (* inverts Graph *)
where "toFunction R = (\<lambda> x . (R ,, x))"
definition kernel where 
-- {* if R is a function, kernel R is the partition of the domain of R
whose each set is made of the elements having the same image through R 
See http://en.wikipedia.org/wiki/Kernel_(set_theory) *} 
"kernel R = Range ((Graph id) O Graph ((op ``)(R^-1)))"
definition part2rel (*from a partition to its equivalence relation*)
:: "'a set set => ('a \<times> 'a) set"
where "part2rel X = \<Union> ((% x . (x \<times> x)) ` X)"

lemma l2: fixes R shows "(runiq R) = (\<forall>x . (R `` {x} \<subseteq> {R ,, x}))"
proof -
show ?thesis using assms runiq_def trivial_def by (metis (hide_lams, no_types) Image_empty RelationProperties.eval_rel.simps equals0D subsetI subset_singletonD the_elem_eq)
qed

definition projector where "projector R =
{ (x,R``{x}) | x . x \<in> Domain R}
(* Graph (% x . (R `` {x}))*)
"
(* compare quotient in Equiv_Relations: here we don't require Range R and Domain R 
to have the same type.
Note that now X//R = Range (projector (R || X)), in the special case of 
R being an equivalence relation *)

lemma l14: fixes f P shows "runiq {(x,f x) | x . P x}"
proof -
let ?F="{(x, f x) | x. P x}"
{
  fix xx have 1: "?F `` {xx} = {b . (xx, b) \<in> ?F}"  
  using Image_singleton Image_def by fast
  also have "... \<subseteq> {f xx}" using assms by fastforce
  finally have "trivial (?F `` {xx})" using trivial_def 1  by fastforce
}
thus ?thesis by (metis (lifting, no_types) RelationProperties.eval_rel.simps l2 trivial_def)
qed

corollary l15: fixes R shows "runiq (projector R)"
proof -
let ?f="%x . R``{x}" let ?P="%x . x\<in>Domain R" let ?F="projector R"
have "?F={(x,?f x) | x . ?P x}" using projector_def by blast
thus ?thesis using l14 by fastforce
qed

(*
lemma fixes x R assumes "equiv (Domain R) R" shows "projector R ,, x = R``{x}"
proof -
let ?D="Domain R" let ?F="op `` R" let ?f="projector R"
have "runiq ?f" using l15 by fast
have 3: "x \<in> ?D" sorry
have 4: "equiv ?D R" sorry
thus "?f ,, x = ?F {x}" sorry
have "?f ,, x = the_elem (?f `` {x})" by force
let ?t="?f `` {x}"
{
  fix X Y assume 1: "X \<in> ?t" assume 2: "Y \<in> ?t"
  have "X \<subseteq> Y" using 1 2 equiv_def assms 3 4 sorry
}
have "trivial ?t" using l14 equiv_def trivial_def try0
using 1 2 projector_def Image_def eval_rel_def sorry
qed
*)

lemma l16: fixes f P xx assumes "P xx" shows
"{(x, f x)| x . P x} ,, xx = f xx"
proof -
let ?F="{(x, f x)| x. P x}" let ?X="?F `` {xx}"
have "?X={f xx}" using Image_def assms by blast
thus ?thesis by fastforce 
qed

corollary l17: fixes R x assumes "x \<in> Domain R" 
shows "projector R ,, x = R `` {x}"
proof -
let ?D="Domain R" let ?f="%xx . (R `` {xx})" let ?r="projector R"
let ?P="%xx . (xx \<in> ?D)" let ?F="{(xx, ?f xx) | xx . ?P xx}"
have 1: "?r=?F" using projector_def by blast
have "?P x" using assms by linarith
hence "?F ,, x = ?f x" using l16 by (metis (mono_tags))
thus ?thesis using 1 by presburger
qed

lemma l26: fixes X R shows "R `` X = R `` (X \<inter> Domain R)"
proof -
show "R `` X = R `` (X \<inter> Domain R)" using Image_def by blast
qed

lemma l18: fixes X::"'a set" fixes R::"('a \<times> 'b) set" shows 
"(X \<inter> Domain R = {}) = (R `` X = {})"
(* and "(R `` X = {}) --> (X \<inter> Domain R = {})" *)
proof -
have "(X \<inter> Domain R = {}) --> (R `` X = {})" using assms l26 by (metis Image_empty)
also have "(R `` X = {}) --> (X \<inter> Domain R = {})" using assms Image_singleton_iff l26  by blast
ultimately show ?thesis by linarith
qed

lemma l18b: fixes x R shows "(x \<in> Domain R) = (R `` {x} \<noteq> {})"
proof - show ?thesis using l18 by blast qed

lemma l19: fixes f P shows "Range {(x, f x)| x. P x}= {f x | x. P x}"
proof -
let ?X="{(x, f x) | x. P x}" let ?LH="Range ?X" let ?RH="{f x | x. P x}"
have "?LH \<subseteq> ?RH & ?RH \<subseteq> ?LH" by blast thus ?thesis by fastforce
qed

corollary l20: fixes R shows "Range (projector R)={R``{x}| x. x\<in>Domain R}"
proof -
let ?D="Domain R" let ?P="% x. x \<in> ?D" let ?p="projector R"
let ?f="%x . R``{x}" let ?X="{(x,?f x)|x. ?P x}" 
let ?lh="Range ?X" let ?rh="{?f x | x. ?P x}"
let ?LH="Range ?p" let ?RH="{?f x| x. x \<in> ?D}"
have "?lh=?LH & ?rh=?RH" using projector_def by fastforce
thus ?thesis using l19 by metis
qed

lemma l27: fixes r assumes "equiv (Domain r) r" 
shows "Range (projector r) = Domain r // r"
proof -
let ?R="projector r" let ?d="Domain r" let ?RH="?d // r" 
let ?f="% x . r `` {x}" let ?LH="Range ?R" let ?MH="{?f x | x. x \<in> ?d}"
have "?RH = (\<Union> x\<in>?d . {?f x})" using Equiv_Relations.quotient_def by blast
hence "?MH = ?RH" using Equiv_Relations.quotient_def by auto
also have "?LH=?MH" using l20 by metis ultimately show "?LH = ?RH" by force
qed

lemma l21: fixes x p assumes "equiv (Domain p) p" 
assumes "x \<in> Domain p"
shows
"{X. ((X \<in> Range (projector p)) & x \<in> X)} = {p `` {x}}"
proof -
let ?P="projector p" let ?D="Domain p" let ?LH="{X. X\<in> Range ?P & x \<in> X}"
let ?XX="p `` {x}" let ?RH="{?XX}"
have 1: "x \<in> ?XX" using equiv_class_self assms by metis
have 2: "?XX \<in> Range ?P" using assms l20 by blast
hence "?XX \<in> ?LH" using assms 1 2 by blast
hence 5: "?RH \<subseteq> ?LH" by fast
{
  fix XX assume "XX \<in> ?LH" hence 
  3: "XX \<in> Range ?P & x\<in>XX" by fast
  have 4: "XX \<in> ?D//p & ?XX \<in> ?D//p" using 3 2 l27 assms by fast
  hence "?XX \<inter> XX \<noteq> {}" using 1 3 by fast 
  hence "?XX=XX" using quotient_disj 4 assms by metis
  hence "XX \<in> ?RH" by fast
}
thus ?thesis using 5 by blast 
qed

lemma l0:  fixes x::'a fixes p::"('a \<times> 'a) set" assumes "equiv (Domain p) p" 
assumes "x \<in> Domain p"
shows
"{X. (X \<in> Range (projector p)) & x \<in> X} = {projector p ,, x}"
proof -
have 1: "equiv (Domain p) p" using assms by auto 
have 2: "x\<in>Domain p" using assms by auto 
have 3: "{X. ((X \<in> Range (projector p)) & x \<in> X)} = {p `` {x}}" 
using 1 2 l21 by (metis (full_types)) (* Weirdly and incredibly SLOWWWWW. WHY?! *)
let ?P="projector p" let ?LH="{X. X \<in> Range ?P & x \<in> X}" let ?RH="{?P ,, x}"
let ?MH="{p `` {x}}"
show ?thesis using 3 assms l17 by metis
qed

definition quotient where "quotient R P Q =
{(p,q). q \<in> (Range (projector Q)) & p \<in> Range (projector P) & p \<times> q \<inter> R \<noteq> {}}
(* {x \<in> Range (projector P) \<times> (Range (projector Q)) . (fst x) \<times> (snd x) \<inter> R \<noteq> {}} *)
"

lemma l1: fixes r x p q
assumes "Domain r \<subseteq> \<Union> Range (projector p)" 
assumes "Range r \<subseteq> \<Union> Range (projector q)"
shows 
"r``{x} \<subseteq> \<Union> ((quotient r p q) `` {X . X \<in> Range (projector p) & x \<in> X})"
proof -
let ?lh="r``{x}" let ?R="quotient r p q" let ?P="projector p"
let ?Q="projector q" let ?Sx="{X. X \<in> Range ?P & x \<in> X}"
let ?RH="?R `` ?Sx" let ?rh="\<Union> ?RH"
{
  fix y assume 0: "y \<in> ?lh"
  hence 1: "(x,y) \<in> r" by fast
  obtain "px" where 5: "px \<in> Range ?P & x \<in> px" using assms 0 by blast
  obtain "qy" where 6: "qy \<in> Range ?Q & y \<in> qy" using assms 0 by blast    
  have 2: "(x,y) \<in> px \<times> qy" using 5 6 by fast
  have 3: "px \<in> Range ?P" using 5 6 by fast
  have 4: "qy \<in> Range ?Q" using 5 6 by fast
  have "(px, qy) \<in> ?R" using quotient_def 1 2 3 4 by force
  hence "qy \<in> ?RH" using 1 2 3 4 by blast
  hence "y \<in> ?rh" using 2 by blast
}
thus ?thesis by fastforce
qed

lemma l3: fixes r q x p assumes "equiv (Domain p) p" 
assumes "runiq (quotient r p q)"
assumes "x \<in> Domain p"
shows 
"(quotient r p q) `` {X . X \<in> Range (projector p) & x \<in> X} 
\<subseteq> {(quotient r p q) ,, ((projector p) ,, x)}"
proof -
(* let ?F="quotient r p q" let ?P="projector p"
let ?XX="{X. X \<in> Range ?P | x \<in> X}"
have "?XX = {?P ,, x}" using l0 assms by fast
thus "?F `` ?XX \<subseteq> {?F ,, (?P ,, x)}" using l2 by (smt assms(2))*)
show ?thesis using l0 l2 assms by (metis (no_types))
qed

lemma l9: fixes Y P shows "snd ` {(x,y) . y\<in>Y & P} \<subseteq> Y"
proof -
let ?R="{(x,y) . y \<in> Y & P}" 
let ?POH="snd ` ?R"
{
  fix y assume "y \<in> snd `?R" (* WHY CAN'T I USE ?POH here ???! *) 
  then obtain z where 1: "z \<in> ?R & y=snd z" by fastforce
  have "y \<in> Y" using 1 by fastforce
}
thus "snd ` ?R \<subseteq> Y" by force
qed

lemma l12: fixes r p q (*probably useless*) 
shows "Range (quotient r p q) \<subseteq> Range (projector q)"
proof -
let ?R="quotient r p q" let ?Q="projector q" let ?P="projector p"
have "?R={(x,y). y \<in> Range ?Q & x \<in> Range ?P & x \<times> y \<inter> r \<noteq> {}}"
using quotient_def by metis
hence "snd ` ?R \<subseteq> (Range ?Q)" using l9 by force
thus ?thesis using Range_snd by metis 
qed

lemma l13: fixes r x p q
assumes "equiv (Domain p) p" 
assumes "runiq (quotient r p q)"
assumes "Domain r \<subseteq> \<Union> Range (projector p)" 
assumes "Range r \<subseteq> \<Union> Range (projector q)"
assumes "x\<in>Domain p"  
shows "r``{x} \<subseteq> (quotient r p q) ,, ((projector p) ,, x)"
proof -
show ?thesis using assms l1 l3 by fast
qed

lemma l4: fixes X f shows "(Graph f) `` X = f ` X"
proof - show ?thesis using assms Graph_def image_def by auto qed

lemma l5: fixes x shows "((Graph id) `` {x}) = {x}"
proof - show ?thesis using id_def l4 by (metis image_id) qed

lemma l6: shows  "(projector (Graph id)) \<supseteq> {(x,{x}) | x . x \<in> Domain (Graph id)}"
proof - show ?thesis using a.projector_def a.l5 by fastforce qed

lemma l7: shows 
"(projector (Graph id)) = {(x,{x}) | x . x \<in> Domain (Graph id)}" and 
"Range {(x,{x})| x. x \<in> Domain (Graph id)}={{x}| x .x \<in> Domain (Graph id)}"
proof 
let ?Id="Graph id" let ?X="Domain ?Id" let ?LH="projector ?Id"
let ?RH="{(x,{x}) | x. x \<in> ?X}"
{
  fix y assume "y \<in> ?LH" then
  have "y \<in> { (x,?Id``{x}) | x . x \<in> ?X}" using projector_def by blast 
  then obtain x where 1: "y=(x,?Id``{x}) & x \<in> ?X" using projector_def by blast
  have "y \<in> ?RH" using l5 1 by fast 
}
thus "?LH \<subseteq> ?RH" by blast
thus "?LH \<supseteq> ?RH" using l6 by blast
show "Range {(x,{x}) | x . x \<in> Domain (Graph id)} 
= {{x} | x . x\<in>Domain (Graph id)}" using Range_snd Range_def by auto 
qed

lemma l10: fixes X i assumes "i \<subseteq> (Graph id)" 
assumes "X \<in> Range (projector i)" shows "trivial X"
proof -
let ?d="Domain i" let ?I="Graph id"
have "X \<in> {i``{x}| x. x \<in> ?d}" using l20 assms by metis
then obtain x where 1: "X=i``{x} & x\<in>?d" by blast
have "i``{x} \<subseteq> ?I ``{x}" using assms by fast
hence "X \<subseteq> ?I `` {x}" using 1 by simp
also have "... = id `{x}" by (metis a.l4)
also have "... = {x}" by auto
finally have "X \<subseteq> {x}" by fast 
thus ?thesis using trivial_def by (metis "1" l18b subset_singletonD the_elem_eq)
qed

(*
lemma l10: fixes X 
(* I assumes "I \<subseteq> (Graph id)" *)
assumes "X \<in> Range (projector (Graph id))" shows "trivial X"
proof - 
let ?Id="Graph id" let ?D="Domain ?Id" let ?XX="{{x}| x .x \<in> ?D}"
have "Range (projector ?Id) = ?XX" using l7 by auto
hence "X \<in> ?XX" using assms by force
then obtain x where 1: "x \<in> ?D & X={x}" by fast
thus "trivial X" using 1 trivial_def by fastforce
qed
*)

lemma l11: fixes x X assumes "{x} \<subseteq> X" and "trivial X" shows "x = the_elem X"
proof -
show ?thesis using assms trivial_def by (metis (mono_tags) in_mono singleton_iff)
qed

lemma l25: fixes x R assumes "x \<in> Domain R"  assumes "runiq R" 
shows "(x, R,,x) \<in> R"
proof -
let ?y="R ,, x" let ?z="(x, ?y)"
have "trivial (R `` {x})" using assms runiq_def by (metis order_refl the_elem_eq trivial_def)
hence "?y \<in> R `` {x}" using assms the_elem_def eval_rel_def trivial_def 
by (smt RelationProperties.eval_rel.simps l18b subset_empty subset_insert)
thus "?z \<in> R" by fast 
qed

lemma l28: fixes r p x q assumes "projector p ,, x \<in> Domain (quotient r p q)"
assumes "runiq (quotient r p q)"
assumes "q \<subseteq> Graph id"
shows "trivial (quotient r p q ,, (projector p ,, x))"
proof -
let ?P="projector p" let ?R="quotient r p q"
let ?Y="?R ,, (?P ,, x)"
have "(?P ,, x, ?R ,, (?P ,, x)) \<in> ?R" using assms l25 by fast
hence "?R ,, (?P ,, x) \<in> Range ?R" by fast
hence 2: "?Y \<in> Range (projector q)" using l12 by blast
thus "trivial ?Y" using l10 2 assms by blast
qed

corollary l29: 
fixes r x p q
assumes "equiv (Domain p) p" 
assumes "runiq (quotient r p q)" (* l23, l24 for that *)
assumes "Domain r \<subseteq> \<Union> Range (projector p)" 
assumes "Range r \<subseteq> \<Union> Range (projector q)"
assumes "x\<in>Domain p"
assumes "runiq r"
assumes "x \<in> Domain r"
assumes "q \<subseteq> Graph id"
assumes "projector p ,, x \<in> Domain (quotient r p q)"
shows "r ,, x = the_elem (quotient r p q ,, (projector p ,, x))"
proof -
let ?P="projector p" let ?R="quotient r p q" let ?Y="?R ,, (?P ,, x)"
have "r `` {x} \<supseteq> {r ,, x}" using assms l2 l18b by (metis subset_singletonD)
hence "{r ,, x} \<subseteq> ?Y" using l13 assms by fast
thus "r ,, x = the_elem ?Y" using l28 assms l11 by fast
qed

definition compatible where 
-- {* Whether R takes each single P-eqclass into a subset of one single Q-eqclass.
This will make more sense when R is a function and P Q are equivalence relations 
over its domain and range, respectively.
However, such requirements are not formally needed, here. *} 
"compatible R P Q = (\<forall> x . (R``(P``{x}) \<subseteq> Q``(R``{x})))"

(*

lemma l23: fixes  E F f assumes "compatible f E F" 
assumes "runiq f" shows "runiq (quotient f E F)"
(* "quotient f E F `` {x} \<subseteq> {(quotient f E F) ,, x}" *)
(* "quotient f E F  = Graph (toFunction (quotient f E F))" *)
(* need a way to say that a relation is a function (i.e., right-unique). 
Which way is most convenient for our needs is to be seen. *)
proof -
show ?thesis using runiq_def assms sorry
qed

type_synonym price = real 
type_synonym allocation = real
type_synonym index = nat
type_synonym bid = "(index \<times> price) set"
definition prices where "prices = \<real>"
definition allocations where "allocations = \<real>"
definition indices where "indices = \<nat>"
(* MC: have to investigate what entities we require 
the currency and the allocation values to be represented by.
Rational and Reals will do, but I guess sub{rings,fields} of a field with 
some order and topology will be sufficient to prove Maskin2. 
Mathematically, this is probably the most interesting issue;
not sure whether there is enough Isabelle library
to tackle that, so for the moment let's stick to \<rat>, \<real>. *)

definition weakdom where "weakdom i a p =
( \<forall> b . \<forall> r .
(r * (a ,, b) - (p ,, b) \<le> r * (a ,, (paste b {(i,r)})) - 
p ,, (paste b {(i,r)})) 
)
"

definition quotientbid 
(* :: " index => ((index \<times> price) set \<times> allocation) set => _ " *)
where
"quotientbid i a =
(*b::(index \<times> price) set*)
(Graph (% b . ((b outside {i}, a ,, b))))"

lemma l24: fixes i a p assumes "weakdom i a p" shows 
"compatible p (part2rel (kernel (quotientbid i a))) (Graph id)" 
proof - (* see LaTeX *)
show ?thesis sorry
qed 

definition reducedbid where "reducedbid i a = part2rel (kernel (quotientbid i a))"

definition Reducedbid where "Reducedbid i a=projector (reducedbid i a)"

definition reducedprice where 
"reducedprice p i a = quotient p (reducedbid i a) (Graph id)" 

theorem fixes i a p b  
assumes "b \<in> Domain p"
assumes "runiq p"
assumes "weakdom i a p"
shows "p ,, b = 
the_elem ((reducedprice p i a) ,, (Reducedbid i a ,, b))"
(* the point is that reducedprice p i a depends on a pair 
(b outside {i}, a ,, b) , given by Reducedbid i a ,, b ;
hence it no longer depends on the whole bid vector b *)
proof -
show ?thesis sorry
qed

lemma fixes v v1 v2 i x p b 
assumes "weakdom i x p"
assumes "lim v1 = v" assumes "lim v2 = v"
assumes "\<exists> k \<in> allocations . lim (
(op -)  
((toFunction x) \<circ> (%j . (paste b {(i, v2 j)})))
((toFunction x) \<circ> (%j . (paste b {(i, v1 j)})))
)
=k" 
shows "v * k = lim (
(* (toFunction p) \<circ> (%j . (paste b {(i, v1 j)}))*)
% j . (p ,, (b +* {(i, v2 j)}) - p ,, ( b +* {(i, v1 j)}))
)"
proof -
show ?thesis sorry
(* Proof stub: 
weak dominance yields
\<forall>j . v1*[x(b2) - x(b1)] \<le> p(b2)-p(b1) \<le> v2*[x(b2) - x(b1)] 
Sandwiched btw two sequences both converging to v*k...
*)
qed

definition weakefficient where "weakefficient a i = 
(\<forall> b::bid . \<exists> v v1 v2 a1 a2. 
(v1 ----> v) &
(v2 ----> v) &
(%j . (a ,, (b +* {(i, v1 j)}))) = (%j . a1) &
(%j . (a ,, (b +* {(i, v2 j)}))) = (%j . a2) &
(a1 \<noteq> a2)
)" 
*)

end

