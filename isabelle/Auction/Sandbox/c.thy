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

theory c
(*MC@CL: I was thinking about moving everything here into RelationProperties, OK?

CL: Makes sense, almost.  I moved "trivial" to SetUtils, as it is not about _relations_.

Once touching RelationProperties keep in mind that it may contain some code
that is redundant with what you have in a.thy and b.thy.  Such as my old computation of 
injective functions.  Some of this may be obsolete now, or it may be worth preserving in 
an "alternative" section; compare Partitions.
*)
imports
  Equiv_Relations
  "../SetUtils"
  "../RelationProperties"
  "../Partitions"
(*"$AFP/Collections/common/Misc"*)

begin

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

(*
definition kernel where
"kernel R=(op `` (R^-1)) ` (Range (projector (Graph id)))"
-- {* if R is a function, kernel R is the partition of the domain of R
whose each set is made of the elements having the same image through R 
See http://en.wikipedia.org/wiki/Kernel_(set_theory) *} 
(* "kernel R = Range ((Graph id) O Graph ((op ``)(R^-1)))" *)
*)

definition part2rel (*from a partition to its equivalence relation*)
:: "'a set set => ('a \<times> 'a) set"
where "part2rel X = \<Union> ((% x . (x \<times> x)) ` X)"





(* BIGSKIP *)

lemma l14: fixes f P shows "runiq {(x,f x) | x . P x}"
proof -
let ?F="{(x, f x) | x. P x}"
{
  fix xx have 1: "?F `` {xx} = {b . (xx, b) \<in> ?F}"  
  using Image_singleton Image_def by fast
  also have "... \<subseteq> {f xx}" using assms by fastforce
  finally have "trivial (?F `` {xx})" using trivial_def 1  by fastforce
}
thus ?thesis by (metis (lifting, no_types) eval_rel.simps runiq_wrt_eval_rel trivial_def)
qed

corollary l15: fixes R::"('a \<times> 'b) set" shows "runiq (projector R)"
proof -
let ?f="%x . R``{x}" let ?P="%x . x\<in>Domain R" let ?F="projector R"
(* let ?P="%x. True" *)
have "?F={(x,?f x) | x::'a . ?P x}" using projector_def by blast
also have "runiq {(x,?f x) | x::'a . ?P x}" using l14 by fast
ultimately show ?thesis by fastforce
qed

lemma l16: fixes f::"'a => 'b" fixes P::"'a => bool" 
fixes xx::"'a" assumes "P xx" shows
"{(x, f x)| x . P x} ,, xx = f xx" 
(*MC: as a corollary of ll88?*)
proof -
let ?F="{(x, f x)| x. P x}" let ?X="?F `` {xx}"
have "?X={f xx}" using Image_def assms by blast
thus ?thesis by fastforce 
qed

corollary l17: fixes R::"('a \<times>'b ) set" fixes xx::"'a" 
assumes "xx \<in> Domain R"
shows "projector R ,, xx = R `` {xx}" 
proof -
let ?D="Domain R" let ?f="%x . (R `` {x})" let ?r="projector R"
let ?P="%xx . (xx \<in> ?D)"
(* let ?P="%x. True" *)
let ?F="{(x, ?f x) | x. ?P x}"
have "?P xx" using assms by fast
hence "?F ,, xx = ?f xx" by (rule l16)
(*MC: try0 and sledgehammer fail here for me! *)
also have "?r=?F" using projector_def by blast
ultimately show ?thesis by presburger
qed

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
using 1 2 by (rule l21)
(* by (metis (full_types)) *)
(* MC: Weirdly and incredibly SLOWWWWW. WHY?! *)
let ?P="projector p" let ?LH="{X. X \<in> Range ?P & x \<in> X}" let ?RH="{?P ,, x}"
let ?MH="{p `` {x}}"
show ?thesis using 3 assms l17 by metis
qed

definition quotient where "quotient R P Q =
{(p,q)| p q. q \<in> (Range (projector Q)) & p \<in> Range (projector P) & p \<times> q \<inter> R \<noteq> {}}
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
show ?thesis using l0 runiq_wrt_eval_rel assms by (metis (no_types))
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

lemma l12: fixes r p q
(* MC: probably useless
   CL@MC: you can find out by putting unused_thms at the end of your theory *)
shows "Range (quotient r p q) \<subseteq> Range (projector q)"
proof -
let ?R="quotient r p q" let ?Q="projector q" let ?P="projector p"
have "?R={(x,y)|x y. y \<in> Range ?Q & x \<in> Range ?P & x \<times> y \<inter> r \<noteq> {}}"
using quotient_def by blast
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
using assms Graph_def image_def by auto

lemma l5: fixes x shows "((Graph id) `` {x}) = {x}"
using id_def l4 by (metis image_id)

lemma l6: "(projector (Graph id)) \<supseteq> {(x,{x}) | x . x \<in> Domain (Graph id)}"
using projector_def l5 by fastforce

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
also have "... = id `{x}" using l4 by metis
also have "... = {x}" by auto
finally have "X \<subseteq> {x}" by fast 
thus ?thesis using trivial_def by (metis "1" Image_within_domain' subset_singletonD the_elem_eq)
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

(* lemma shows "runiq (projector R O (Graph (%X . (THE x. x\<in>X))))"
using assms projector_def relcomp_def Graph_def runiq_def  *)

lemma l28: fixes r p x q assumes "projector p ,, x \<in> Domain (quotient r p q)"
assumes "runiq (quotient r p q)"
assumes "q \<subseteq> Graph id"
shows "trivial (quotient r p q ,, (projector p ,, x))"
proof -
let ?P="projector p" let ?R="quotient r p q"
let ?Y="?R ,, (?P ,, x)"
have "(?P ,, x, ?R ,, (?P ,, x)) \<in> ?R" using assms eval_runiq_rel by fast
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
have "r `` {x} \<supseteq> {r ,, x}" using assms runiq_wrt_eval_rel Image_within_domain' by (metis subset_singletonD)
hence "{r ,, x} \<subseteq> ?Y" using l13 assms by fast
thus "r ,, x = the_elem ?Y" using l28 assms singleton_sub_trivial_uniq by fast
qed

definition compatible where 
-- {* Whether R takes each single P-eqclass into a subset of one single Q-eqclass.
This is usually asked when R is a function and P Q are equivalence relations 
over its domain and range, respectively.
However, such requirements are not formally needed, here. *} 
"compatible R P Q = (\<forall> x . (R``(P``{x}) \<subseteq> Q``(R``{x})))"

lemma l31: assumes "runiq f" assumes "(x,y)\<in>f" shows "y=f,,x" 
using assms runiq_wrt_eval_rel runiq_def eval_rel_def
insert_not_empty order_trans subset_singletonD
by (smt Image_singleton_iff equals0D singletonE)

lemma l32: shows "runiq R = (\<forall> x . trivial (R``{x}))"
using assms by (metis runiq_alt)

lemma l33: assumes "(\<forall> x y1 y2. (x,y1) \<in> R & (x,y2)\<in>R \<longrightarrow> y1=y2)"
shows "runiq R"
using assms runiq_def 
proof -
{
  fix x y assume 0: "y \<in> R `` {x}"
(*  hence "\<forall> y2 \<in> R``{x}. y2\<in>{y}" using assms l32 runiq_def ll1 by blast *)
  hence "R `` {x} \<subseteq> {y}" using assms l32 runiq_def runiq_alt by blast
  hence "trivial (R``{x})" using trivial_def assms 0 by (metis order_refl the_elem_eq trivial_subset)
}
thus ?thesis using l32 trivial_def by blast
qed

lemma l35: shows "projector (Graph id)={(x,{x})|x. True}" (is "?LH=?RH")
using projector_def Graph_def id_def
proof -
let ?I="Graph id" let ?II="{(x,x)|x. True}" let ?D="Domain ?I"
let ?LH2="projector ?II"
term "Domain ?I"
let ?RH2="{(x, ?I `` {x})|x. x\<in>?D}"
let ?RH1="{(x,{x})|x. x\<in>?D}"
have "?LH \<supseteq> ?RH2" using assms projector_def Graph_def id_def by fast
also have "?LH \<subseteq> ?RH2" using assms projector_def Graph_def id_def by auto
ultimately have "?LH = ?RH2" by fast
also have "... = ?RH1" by (metis l5)
also have "... = ?RH" by (metis Image_within_domain' insert_not_empty l5)
ultimately show ?thesis by presburger
qed

(*
lemma l36: fixes R::"('a \<times> 'b) set"
assumes "(x,y) \<in> part2rel (kernel R)" shows "R``{x} \<inter> (R `` {y}) \<noteq> {}"
using part2rel_def kernel_def Image_def assms 
proof -
let ?I="projector (Graph id)"
have 2: "Range ?I={{x}|x::('b). True}" using l35 by auto
let ?k="(op `` (R^-1)) ` (Range ?I)" let ?E="\<Union> ((% x . (x \<times> x)) ` ?k)"
have "(x,y) \<in> ?E" using assms part2rel_def kernel_def by metis then
obtain X where 0: "(x,y) \<in> (X \<times> X) & X \<in> ?k"
using part2rel_def assms by (smt UnionE imageE)
obtain Z::"'b set" where 1: "X = R^-1 `` Z & Z \<in> Range ?I" using 0 kernel_def Image_def Range_def 
by (smt image_iff)
have "Z \<in> {{x}|x::'b. True}" using 1 2 by auto then
obtain z::'b where 3: "Z={z} & True" by blast
have "x \<in> R^-1 `` {z} & y \<in> R^-1 `` {z}" using 3 0 1 by blast
hence "z \<in> R `` {x} & z \<in> R `` {y}" by fastforce
thus ?thesis by auto
qed
*)

lemma l23: fixes g p q assumes lc: "compatible g p q" 
assumes lr: "runiq g" 
assumes lt: "trans p"
assumes ls: "sym p"
assumes le: "equiv (Domain q) q"
shows "runiq (quotient g p q)" (is "runiq ?G")
(* "quotient f E F `` {x} \<subseteq> {(quotient f E F) ,, x}" *)
(* "quotient f E F  = Graph (toFunction (quotient f E F))" *)
(* need a way to say that a relation is a function (i.e., right-unique). 
Which way is most convenient for our needs is to be seen. *)
proof -
let ?r="runiq" let ?pr="projector" let ?R="Range"
let ?P="?pr p" let ?Q="?pr q" let ?RP="?R ?P" let ?RQ="?R ?Q"
let ?GG="{(x,y)| x y. y \<in> ?RQ & x \<in> ?RP & x \<times> y \<inter> g \<noteq> {}}"
{
  fix X Y1 Y2 assume "(X, Y1) \<in> ?GG" hence 3: "X \<in> ?RP & Y1 \<in> ?RQ & X \<times> Y1 \<inter> g \<noteq> {}" by simp
  hence "X \<in> Range {(x, p `` {x})|x. x\<in> Domain p}" using projector_def by metis
  then obtain x where 10: "x\<in> Domain p & X = p``{x}" 
  using projector_def Range_def by blast
  obtain x1 y1 where 1: "(x1, y1) \<in> X \<times> Y1 \<inter> g" using 3 by auto  
  assume "(X, Y2) \<in> ?GG" hence 4: "Y2 \<in> ?RQ & X \<times> Y2 \<inter> g \<noteq> {}" by simp
  then obtain x2 y2 where 2: "(x2, y2) \<in> X \<times> Y2 \<inter> g" by blast
  have "x1 \<in> X & x2 \<in> X" using 1 2 by fastforce 
  hence "x1 \<in> p `` {x} & x2 \<in> p `` {x}" using 10 by auto
  hence "(x1,x) \<in> p & (x,x2) \<in> p" using ls by (metis Image_singleton_iff symD)
  hence "(x1,x2) \<in> p" using lt transD by metis
  hence "{x2} \<subseteq> p `` {x1}" by fastforce hence
  "g `` {x2} \<subseteq> g `` (p `` {x1})" by blast
  also have "... \<subseteq> q `` (g `` {x1})" using lc compatible_def by metis
  also have "... \<subseteq> q `` {g ,, x1}" using lr 1 by (metis Image_empty equals0D runiq_wrt_eval_rel subsetI subset_singletonD)
  also have "... \<subseteq> q `` {y1}" using 1 l31 lr by fast
  ultimately have "{y2} \<subseteq> q `` {y1}" using 2 l31 by blast
  hence "(y1,y2) \<in> q & y1 \<in> Y1 & y2 \<in> Y2 & Y1 \<in> (Domain q)//q
  & Y2 \<in> (Domain q)//q & equiv (Domain q) q" using 1 2 3 4 le l27 by auto
  hence "Y1=Y2" by (metis quotient_eq_iff)
}
hence "runiq ?GG" using l33 by smt
thus ?thesis using quotient_def by metis
qed

lemma assumes "runiq f" assumes "compatible f p q" shows "
(\<forall> x. (f `` (p `` {x})) \<subseteq> q `` {f ,, x})" 
using assms l32 trivial_def compatible_def by 
(metis (hide_lams, no_types) Image_empty eval_rel.simps empty_subsetI subset_empty subset_singletonD)

lemma assumes "runiq f" 
assumes "\<forall> x. (f `` (p `` {x}) \<subseteq> q `` {f ,, x})" 
shows "\<forall>x \<in> Domain f . (f `` (p `` {x}) \<subseteq> q `` (f `` {x}))"
using assms by (metis Image_runiq_eq_eval)

lemma l34: shows "compatible r p q = (\<forall> x\<in> Domain p .(r `` (p `` {x}) \<subseteq> q `` (r ``{x})))"
using compatible_def by fast

lemma l37: shows "(P outside X) outside X=P outside X" using assms Outside_def 
by auto (*MC: generalize to X Y X \<union> Y; make it a corollary of ll51? *)

lemma l38: shows "P +* Q = (P outside (Domain Q)) +* Q" 
(*MC: generalize to X s.t. X \<inter> Domain P \<subseteq> Domain Q*)
proof -
let ?D="Domain Q" let ?p="P outside ?D" let ?LH="P +* Q" let ?RH="?p +* Q"
have "?p +* Q = ?p \<union> Q" using paste_def l37 by metis
thus ?thesis using paste_def by blast
qed

corollary l39: shows "R = (R outside {x}) \<union> ({x} \<times> (R `` {x}))" 
using restrict_to_singleton outside_union_restrict by metis

corollary l40: shows "R = (R outside {x}) +* ({x} \<times> (R `` {x}))" 
by (metis paste_outside_restrict restrict_to_singleton)

definition update where "update P Q = P +* (Q || (Domain P))"
(*MC: no longer used, but possibly interesting: behaves like +* (paste), but
without enlarging P's Domain. Compare with fun_upd *)

notation update (infix "+^" 75)

lemma l43: shows "\<Union> ((op `` R) ` X)= R ``(\<Union> X)" using Image_def by blast

lemma l44: shows "\<Union> Range (projector R) \<supseteq> Range R" 
using projector_def Image_def by blast

lemma l45: shows "Range (projector R) \<subseteq> Pow (Range R)" (is "?LH \<subseteq> ?RH")
proof -
have "?LH={R``{x}|x. x \<in> Domain R}" by (metis l20) 
also have "... \<subseteq> Pow (Range R)" by fast
ultimately show ?thesis by simp
qed

corollary l46: shows "\<Union> Range (projector R) = Range R" 
using l44 l45 by (metis Union_Pow_eq Union_mono antisym)

lemma l47: shows "Domain (part2rel XX)=\<Union> XX & \<Union> XX = Range (part2rel XX)" 
using part2rel_def by blast

(*
lemma l48: shows "Domain (part2rel (kernel P)) = Domain P" 
proof -
let ?D=Domain let ?k="kernel" let ?p=projector let ?r=part2rel 
let ?f=P let ?XX="?k ?f" let ?Q="?r ?XX" let ?R="?f^-1"
have "?D ?Q= \<Union> ?XX" using l47 by metis
also have "... = ?R `` (\<Union> (Range (?p (Graph id))))" using kernel_def l43 by metis
also have "... = ?R `` (Range (Graph id))" using l46 by metis
also have "... = ?R `` (Domain ?R)" using Graph_def by fastforce
also have "... = Range ?R" by fast
ultimately show "?D ?Q=Domain ?f" by simp
qed
*)

lemma assumes "runiq R" shows 
"(\<forall> x y1 y2. (x,y1) \<in> R & (x,y2)\<in>R \<longrightarrow> y1=y2)"
using assms l31 by metis

definition runiqer 
::"('a \<times> 'b) set => ('a \<times> 'b) set"
(* MC: A choice map to solve a multi-valued relation 
into a function of maximal domain *)
where "runiqer R={ (x, THE y. y \<in> R `` {x})| x. x \<in> Domain R }"
(* MC: alternatively: "...| x. True }" *)

lemma l30: fixes R shows "runiq { (x, THE y. y \<in> R `` {x})| x. x \<in> Domain R }"
(is "runiq ?f") 
using assms runiq_def l14 by fast

corollary shows "runiq (runiqer R)" using l30 runiqer_def by metis

lemma ll47: assumes "finite R" shows "card (Domain R) \<le> card R & card (Range R) \<le> card R"
(is "card ?D \<le> card R & card ?R \<le> card R")
(* MC: Could be weakened by asking only finite (Domain R) (resp Range R) *)
proof -
have "?D = fst ` R & ?R = snd ` R" by force
thus ?thesis using card_image_le assms by metis
qed

lemma ll65: fixes R shows "kernel R = {R^-1 `` {y}|y. y\<in> Range R}"
(is "?LH=?RH")
proof -
have "?LH = {R^-1 `` Y| Y. Y \<in> finestpart (Range R)}"
using kernel_def by (metis image_Collect_mem)
also have "...={R^-1 `` Y| Y. Y \<in> {{y}|y. y\<in> Range R}}" using ll64 by metis
also have "...= ?RH" by blast ultimately show ?thesis by presburger
qed

lemma shows "kernel R = {R^-1 `` {y}| y. y\<in> Range R}"
proof -
let ?k=kernel let ?r=Range let ?f=finestpart let ?R="?r R" 
let ?RH="{R^-1 ``{y}| y. y \<in> ?r R}" 
let ?LH="(op `` (R^-1)) ` (?f ?R)"
{  
  fix y assume "y \<in> ?r R" hence "{y} \<in> ?f ?R" 
  using finestpart_def by auto hence "R^-1 `` {y} \<in> ?LH"  by blast
} 
then have 0: "?LH \<supseteq> ?RH" by blast
{
  fix Y assume "Y \<in> ?f ?R" also have "?f ?R={{y}| y. y \<in> ?R}" using ll64 by blast
  ultimately obtain y where 
  1: "Y={y} & y \<in> ?R" using finestpart_def by auto
  have "R^-1 `` Y \<in> ?RH" using 1 by blast
}
then have "?LH \<subseteq> ?RH" by blast 
also have "?LH = ?k R" using kernel_def by auto
ultimately show ?thesis using 0 by force
qed

lemma ll69: assumes "trivial t" "t \<inter> X \<noteq> {}" shows "t \<subseteq> X" using trivial_def assms 
by (smt disjoint_iff_not_equal in_mono singleton_iff subsetI)

lemma ll70: assumes "runiq f" "trivial Y" shows "trivial (f `` (f^-1 `` Y))"
proof -
let ?g="f^-1" let ?X="?g``Y" let ?T="f``?X" let ?t=trivial
{
  fix x have 0: "?t (f``{x})" using assms by (metis l32) 
  assume "x \<in> ?X" hence "f``{x} \<inter> Y \<noteq> {}" using assms Image_def by fast
  hence "f``{x} \<subseteq> Y" using ll69 0 by metis
}
hence "?T \<subseteq> Y" by blast thus ?thesis using assms by (metis trivial_subset)
qed

lemma ll71: fixes f Y assumes "runiq f" shows "f `` (f^-1 `` Y) \<subseteq> Y" 
proof -
let ?g="f^-1" let ?X="?g `` Y" let ?LH="f `` ?X" let ?I="?g O f" let ?t=trivial
{
  fix y::"'b" 
  have "?I``{y} = f``(?g `` {y})" by fast
  also have "?t {y}" by (metis order_refl the_elem_eq trivial_def)
  then have "?t (f``(?g``{y}))" 
  using ll70 assms by auto
  ultimately have "?t (?I``{y})" by auto
  hence "?I``{y} \<subseteq> {y}" using ll69 by auto 
}
hence "?I``Y \<subseteq> Y" by blast thus ?thesis by fast
qed

lemma ll68: assumes "runiq f" "y1 \<in> Range f" shows 
"(f^-1 `` {y1} \<inter> f^-1 `` {y2} \<noteq> {}) = (f^-1``{y1}=f^-1``{y2})"
using assms ll71 by fast
(* ll66 by (smt Un_Int_assoc_eq) *)

lemma ll66: assumes "runiq f" "y1 \<in> Range f" "y2 \<in> Range f" shows 
"(f^-1 `` {y1} \<inter> f^-1 `` {y2} \<noteq> {}) = (y1=y2)"
using assms ll71 by fast

lemma ll72: assumes "runiq f" shows "is_partition {f^-1 `` {y}| y. y\<in> Range f}" 
proof -
let ?i=is_partition let ?R=Range let ?r=runiq let ?g="f^-1"
let ?P="{?g `` {y}| y. y\<in> ?R f}" have "?thesis = (\<forall> X\<in> ?P . \<forall> Y \<in> ?P . (X \<inter> Y \<noteq> {} \<longleftrightarrow> X=Y))" 
using is_partition_def by (rule exE_realizer)
thus ?thesis using ll68 assms by fast 
qed

lemma ll79: assumes "runiq f" shows "kernel f partitions (Domain f)"
proof -
have 0: "Domain f = \<Union> kernel f" using ll65 by blast
have "is_partition (kernel f)" using assms ll72 ll65 by metis
thus ?thesis using 0 is_partition_of_def by metis
qed

lemma ll73: fixes x y XX shows "(x,y) \<in> part2rel XX = (EX X. X\<in>XX & x\<in>X & y\<in>X)"
using assms part2rel_def by blast

lemma ll74: fixes XX shows "refl_on (Union XX) (part2rel XX)" 
proof -
let ?R="part2rel XX" let ?X="\<Union> XX" have 
0: "?R \<subseteq> ?X \<times> ?X" using l47 by fastforce
{fix x assume "x \<in> ?X" then have "(x,x)\<in>?R" using ll73 by fast} 
thus ?thesis using refl_on_def 0 by metis
qed

lemma ll75: fixes XX shows "sym (part2rel XX)" 
using assms ll73 sym_def is_partition_def 
proof -
let ?R="part2rel XX" {fix x y assume "(x,y)\<in>?R" hence "(y,x)\<in>?R" using ll73 by metis}
thus ?thesis using sym_def by blast
qed

lemma ll76: assumes "is_partition XX" shows "trans (part2rel XX)" 
proof -
let ?f=part2rel let ?R="?f XX"
{
  fix x y z assume "(x,y) \<in> ?R" then obtain X1 where 
  1: "X1\<in>XX & x\<in>X1 & y\<in>X1" using ll73 by metis 
  assume "(y,z)\<in>?R" then obtain X2 where 
  2: "X2\<in>XX & y\<in>X2 & z\<in>X2" using ll73 by metis
  have "{y} \<subseteq> X1 \<inter> X2" using 1 2 by fast
  hence "X1=X2" using assms 1 2 by (metis empty_iff is_partition_def singleton_iff subset_empty)
  hence "(x,z)\<in>?R" using ll73 1 2 by fast
}
thus ?thesis using trans_def by blast
qed

lemma ll77: assumes "is_partition XX" shows "equiv (Union XX) (part2rel XX)" 
using assms ll74 ll75 ll76 equiv_def by fast

corollary ll78: assumes "runiq f" shows "equiv (Domain f) (part2rel (kernel f))"
using assms ll77 ll79 is_partition_of_def by metis

lemma ll59: shows "P O Q={(x,z) | x z. (EX y. (x,y) \<in> P & (y,z)\<in>Q)}"
using assms relcomp_def by blast

lemma ll60: shows "P O Q O R = 
{(v,z)| v z. EX x y. (v,x) \<in> P & (x,y) \<in> Q & (y,z)\<in>R}" by blast

lemma ll61: assumes "refl_on X P" "x\<in>X" shows "x \<in> P``{x}" using refl_on_def assms
by (metis Image_singleton_iff)

lemma ll62: fixes x X assumes "equiv (Domain p) p" "X \<in> Range (projector p)"
shows "(x,X) \<in> projector p = (x \<in> X)" (is "?LH = ?RH")
proof -
let ?p=projector let ?P="?p p" let ?d=Domain let ?r=Range 
have 0: "?P = {(x, p``{x})| x. x\<in> ?d p}" using projector_def by blast
also have "refl_on (?d p) p" using assms equiv_def by blast 
(* MC: for ?LH \<longrightarrow> ?RH, reflexivity suffices *)
ultimately also have "?LH \<longrightarrow> x \<in> p``{x}" using ll61 by fastforce
ultimately have 3: "?LH \<longrightarrow> ?RH" by force 
have "?r ?P = {p``{x}| x. x \<in> ?d p}" using l20 by metis then obtain xx where 
1: "X=p``{xx} & xx \<in> Domain p" using assms by auto
{
  assume ?RH hence "x \<in> p``{xx}" using assms 1 by metis
  hence "(xx,x) \<in> p" by fast hence "p``{x}=p``{xx}" using assms by (metis equiv_class_eq_iff)
  hence "(x,X) \<in> ?P" using 1 0 by auto
}
thus ?thesis using 3 by linarith
qed

lemma ll63: assumes "equiv (Domain p) p" "equiv (Domain q) q"
shows "quotient r p q = (projector p)^-1 O r O (projector q)"
proof -
let ?p=projector let ?P="?p p" let ?Q="?p q" let ?q=quotient let ?D=Domain
let ?PP="?P ^-1" let ?R=Range let ?LH="?q r p q" let ?RH="?PP O r O ?Q" have 
1: "\<forall> X\<in> ?D ?PP. \<forall> x. ((x \<in> X) = ((X,x) \<in> ?PP))" using ll62 assms(1) by fast have 
2: "\<forall> X\<in> ?R ?Q. \<forall> x. ((x \<in> X) = ((x,X) \<in> ?Q))" using ll62 assms(2) by fast
have "?RH = {(X,Y)| X Y. EX x y. (X,x) \<in> ?PP & (x,y) \<in> r & (y,Y)\<in> ?Q}" by blast
also have "... = 
{(X,Y)| X Y. EX x y. X \<in> ?D ?PP & (X,x) \<in> ?PP & (x,y) \<in> r & (y,Y)\<in> ?Q}" by force
also have "... = 
{(X,Y)| X Y. EX x y. X \<in> ?D ?PP & x \<in> X & (x,y) \<in> r & (y,Y)\<in> ?Q}" using 1 by auto
also have "... = 
{(X,Y)| X Y. EX x y. X \<in> ?D ?PP & x \<in> X & (x,y) \<in> r & Y \<in> ?R ?Q & y \<in> Y}" using 2 by auto
also have "... = {(X,Y)| X Y. X\<in> ?D ?PP & Y \<in> Range ?Q & X \<times> Y \<inter> r \<noteq> {}}" by auto
also have "... = {(X,Y)| X Y. X\<in> Range ?P & Y \<in> Range ?Q & X \<times> Y \<inter> r \<noteq> {}}" by auto
also have "... = quotient r p q" using quotient_def by fastforce
ultimately show ?thesis by presburger
qed


lemma ll51: shows "(P \<union> Q) outside X = P outside X \<union> (Q outside X)"
using Outside_def Un_assoc
proof -
  let ?R="P \<union> Q" let ?r="Range" let ?rp="?r P" let ?rq="?r Q" let ?rr="?r ?R"
  have "?R - (X \<times> ?rr)= P - (X \<times> ?rr) \<union> (Q - (X \<times> ?rr))" by fast
  also have "... = P - (X \<times> ?rp) \<union> (Q - (X \<times> ?rr))" by blast
  also have "... = P - (X \<times> ?rp) \<union> (Q - (X \<times> ?rq))" by blast
  ultimately show ?thesis using Outside_def by metis
qed

lemma ll52: shows "P outside (X \<union> Y) = (P outside X) outside Y"
using assms Outside_def
proof -
  let ?R="Range" let ?r="?R P" have "(P outside X) outside Y=
  P - (X \<times> ?r) - (Y \<times> ?r)" using Outside_def by auto
  also have "... = P outside (X \<union> Y)" using Outside_def by fastforce
  ultimately show ?thesis by presburger
qed

lemma ll53: shows "(P +* Q) +* R = P +* (Q +* R)" (is "?LH = ?RH")
proof -
let ?D="Domain" let ?dp="?D P" let ?dq="?D Q" let ?dr="?D R" have 
"?LH=(P outside ?dq \<union> Q) outside ?dr \<union> R" using paste_def by metis also have 
"...= ((P outside ?dq) outside ?dr) \<union> (Q outside ?dr) \<union> R" using ll51 by metis
also have "...= (P outside (?dq \<union> ?dr)) \<union> (Q outside ?dr) \<union> R" using ll52 by metis 
also have "...= (P outside (?D (Q +* R))) \<union> (Q +* R)" using paste_def 
by (metis Domain_Un_eq paste_Domain sup_assoc sup_commute sup_left_commute)
ultimately show ?thesis using paste_def by blast
qed

lemma ll54: assumes "(Domain P \<subseteq> Domain Q)" shows "(P +* Q=Q)"
proof -
  let ?D="Domain" let ?R="Range" have "P - (?D P \<times> (?R P))={}" by fast
  hence "P outside (?D Q)={}" using Outside_def assms by fast
  thus ?thesis using assms paste_def Outside_def by blast
qed

lemma ll55: assumes "(P +* Q=Q)" shows "(Domain P \<subseteq> Domain Q)"
using assms paste_def Outside_def by blast

lemma ll56: shows "(Domain P \<subseteq> Domain Q) = (P +* Q=Q)"
using ll54 ll55 by metis


lemma ll80: "\<Union> (kernel R) = Domain R" 
proof -
have "\<Union> {R^-1 `` {y}|y. y\<in> Range R} = Domain R" by blast
thus ?thesis using ll65 by metis
qed

lemma ll82: shows "R \<supseteq> R+*({x} \<times> (R``{x}))" by (metis 
Un_least Un_upper1 outside_union_restrict paste_def restrict_to_singleton restriction_is_subrel)

lemma ll83: shows "R \<subseteq> R +* ({x} \<times> (R``{x}))" using 
l40 l38 paste_def Outside_def by fast

corollary ll84: shows "R = R +* ({x} \<times> (R``{x}))" using ll82 ll83 by force

definition graph where "graph X f = {(x, f x) | x. x \<in> X}" 
(* duplicates Function_Order, which is otherwise unneeded,
and I don't have enough hardware to import *)

lemma ll85: assumes "runiq f" shows "runiq (f^-1 O f)"
proof -
let ?g="f^-1" let ?it="?g O f" have "\<forall> Y. f``(?g``Y) = ?it``Y" by fast
thus ?thesis using ll70 assms runiq_def by metis
qed

lemma ll81: fixes R f assumes "R\<subseteq>f" "runiq f" "Domain f \<subseteq> Domain R" shows "f=R" 
proof -
let ?d=Domain let ?r=Range let ?u=runiq let ?t=trivial
{
  fix z::"'a \<times> 'b" let ?x="fst z" let ?y="snd z" assume 
  1: "z\<in>f" hence "?x\<in>?d f" using Domain_def by (metis fst_eq_Domain imageI) hence 
  0: "?x \<in> ?d R" using assms(3) by blast
  hence "R``{?x} \<subseteq> f``{?x} & R``{?x} \<noteq> {}" using assms(1) by fast
  also have "?t (f``{?x})" using assms(2) runiq_def by (metis l32)
  ultimately have "f``{?x} \<subseteq> R``{?x}" using 0 trivial_def by (metis (full_types) inf_absorb2 ll69)
  also have "?y \<in> f``{?x}" using Image_def 1 by auto
  ultimately have "?y \<in> R``{?x}" by blast hence "z \<in> R" using 0 by fastforce
}
thus ?thesis using assms(1) by fast
qed

lemma ll94: fixes R::"('a \<times> 'b) set" shows "graph (Range R) id \<subseteq> (R^-1 O R)"
proof -
let ?r=Range {fix z::"'b \<times> 'b" assume "z \<in> graph (?r R) id" hence 
  "z \<in> {(x, id x)|x . x \<in> ?r R}" using graph_def by blast then obtain x where
  0: "z = (x, id x) & x \<in> ?r R" by fast
  have "z \<in> R^-1 O R" using 0 by auto }
thus ?thesis by blast
qed

lemma ll86: assumes "runiq f" shows "f^-1 O f = graph (Range f) id"
proof -
let ?p=projector let ?k=kernel let ?u=part2rel let ?d=Domain let ?r=Range
let ?G=Graph let ?i="?G id" let ?I="?p ?i" let ?u=runiq let ?g=graph
let ?if="f^-1" let ?II="?if O f" have "?d ?II \<subseteq> ?r f" by fast
also have "?d (?g (?r f) id) \<supseteq> ?r f" using graph_def by fast
ultimately have "?d ?II \<subseteq> ?d (?g (?r f) id)" by auto
moreover have "?g (?r f) id \<subseteq> ?II" using ll94 by blast
moreover have "?u ?II" using assms(1) ll85 by fast
ultimately show "?II = ?g (?r f) id" using ll81 by metis
qed

lemma ll90: shows "(\<Union> ((projector R)``X)) \<supseteq> R``X" using projector_def by blast

lemma ll88: assumes "P xx" shows "{(x, f x)|x. P x}``{xx} = {f xx}"
using Image_def assms by blast

lemma ll89: fixes X::"'a set" fixes R::"('a \<times> 'b) set" shows "\<Union> ((projector R)``X) \<subseteq> R``X" 
(* MC: shorten this proof *)
proof -
let ?p=projector let ?f="?p R" let ?d=Domain let ?ff="{(x, R``{x})|x . x\<in>?d R}" have 
0: "?f = ?ff" using projector_def by blast
have "?d ?ff = ?d R" by auto
{
  fix x::"'a" assume 
  1: "x \<in> X"
  have "x \<notin> ?d ?f \<longrightarrow> ?f `` {x}   \<subseteq> {R``{x}}" by auto
  also have "?d ?f = ?d R" using 0 by blast
  ultimately have 2: "x \<notin> ?d R \<longrightarrow> ?f `` {x} \<subseteq> {R``{x}}" by presburger
  {
    assume "x \<in> ?d R" 
    then have "?ff``{x} = {R``{x}}" using ll88 by blast
    then have "?f `` {x} \<subseteq> {R``{x}}" using 0 by simp
  }
  then have  "\<Union> (?f `` {x}) \<subseteq> R``X" using 1 2 by fast
}
thus ?thesis by blast
qed

corollary ll91: shows "(\<Union> ((projector R)``X)) = R``X" using ll90 ll89 
assms by (metis antisym_conv)

lemma ll87: shows "runiq ((projector Id)^-1)"
proof -
let ?u=runiq let ?p=projector let ?i=Id let ?I="?p ?i" let ?Ii="?I^-1"
let ?f="{(x,{x})|x. x\<in>UNIV}" let ?g="?f^-1" have "?g={({x},x)|x. x\<in>UNIV}" by blast
moreover have "... = {(X, the_elem X)|X. X \<in> finestpart UNIV}" using finestpart_def by fastforce
also have "runiq ..." using l14 by fast finally have "runiq ?g" by blast
also have "?I=?f" using projector_def by auto ultimately show "runiq ?Ii" by metis
qed

lemma ll92: shows "Range ((projector Id)^-1)=UNIV" using projector_def by fastforce

corollary ll93: shows "(((projector Id) ^-1)^-1) O ((projector Id) ^-1)=graph UNIV id"
using ll86 ll87 ll92 by metis

lemma ll36: shows "Graph f=graph UNIV f"
proof -
have "{(x, f x)|x. x\<in>UNIV}={(x, f x)|x. True}" by force 
thus ?thesis using Graph_def graph_def by metis
qed

corollary ll95: shows "Graph id=Id & Id=graph UNIV id" using graph_def Graph_def
proof -
let ?it="{(x, id x)|x. x\<in>UNIV}" have "Id = ?it" using Graph_def Id_def by auto
thus ?thesis using ll36 graph_def by metis
qed 

corollary ll96: shows "(projector Id) O ((projector Id)^-1) = Id"
using ll93 ll95 by fastforce

lemma ll50: shows "(P +* Q)``(Domain Q \<inter> X) = Q `` (Domain Q \<inter> X)" 
using paste_def Outside_def Image_def Domain_def
proof -
  let ?D="Domain" let ?dq="Domain Q"
  have "(P outside ?dq) `` (?dq \<inter> X) \<subseteq> {}" 
  using Image_outside_domain outside_reduces_domain
  by (metis Diff_disjoint empty_subsetI inf_assoc inf_bot_right inf_commute)
  thus ?thesis using paste_def by blast
qed

lemma shows "sym (graph X id)" 
proof -
have "graph X id={(x,id x)|x. x\<in> X}" using graph_def by blast
also have "sym {(x,id x)|x. x\<in>X}" using sym_def by auto
ultimately show ?thesis by presburger
qed

lemma ll02: assumes "runiq f" "runiq g" shows "runiq (f O g)"
proof -
let ?u=runiq let ?h="f O g"
{
  fix x z1 z2 assume "(x,z1) \<in> ?h" then obtain y1 where 
  1: "(x,y1) \<in> f & (y1,z1) \<in> g" by fast
  assume "(x,z2) \<in> ?h" then obtain y2 where 
  2: "(x,y2) \<in> f & (y2,z2) \<in> g" by fast
  have "y1 = y2" using assms(1) 1 2 by (metis l31)
  then have "z1=z2" using assms(2) 1 2 l31 by metis
}
thus ?thesis by (metis l33)
qed

lemma ll04: assumes "runiq P" shows "projector (P O Q) = P O (projector Q)"
(*TODO@MC: modularize this proof *)
proof -
let ?u=runiq let ?t=trivial let ?k=kernel let ?c=part2rel 
let ?d=Domain let ?r=Range let ?G=Graph let ?g=graph let ?p=projector
let ?pp="%R.{ (x,R``{x}) | x . x \<in> ?d R}" have 
10:"{(x, P,,x)|x. x\<in> P^-1``(?d Q)} \<subseteq> P" using assms  eval_runiq_rel by fast
have "\<forall> X. (%x. P,,x)`(?d P \<inter> X)=P``(?d P \<inter> X)" 
using Image_runiq_eq_eval assms by fast 
moreover have "\<forall> Y. ?d P \<inter> P^-1``Y=P^-1``Y" by fast
ultimately have "\<forall>Y. (%x. P,,x)`(P^-1``Y)=P``(P^-1``Y)" by metis 
hence "\<forall>Y. (%x. P,,x)`(P^-1``Y) \<subseteq> Y" using assms ll71 by metis
hence 9:"{(y,Q``{y})|y. y\<in>(%x. P,,x)`(P^-1``(?d Q))} \<subseteq> ?pp Q" by blast
have "?pp (P O Q) = {(x, Q ``(P``{x}))| x. x \<in> P^-1``(?d Q)}" by fast
also have "... = {(x, Q``{P,,x})|x. x\<in>P^-1``(?d Q)}"
using Image_runiq_eq_eval assms by force
also have "... = {(x, P,,x)|x. x\<in> P^-1``(?d Q)} O 
{(y,Q``{y})|y. y\<in>(%x. P,,x)`(P^-1``(?d Q))}" by blast
also have "... \<subseteq> {(x, P,,x)|x. x\<in> P^-1``(?d Q)} O (?pp Q)" using 9 by force
also have "... \<subseteq> P O (?pp Q)" using 10 by blast
also have "runiq ..." using assms ll02 l15 by (metis projector_def)
ultimately have "?pp (P O Q) \<subseteq> P O (?pp Q) & runiq (P O (?pp Q))" by fastforce
also have "?d (?pp (P O Q)) \<supseteq> ?d (P O (?pp Q))" by auto
ultimately have "?pp (P O Q) = P O (?pp Q)" using ll81 by smt
thus ?thesis using projector_def by metis
qed

lemma ll01: shows 
"part2rel (kernel R)={(x1, x2)|x1 x2 . EX y. {x1,x2} \<subseteq> R^-1``{y}}"
proof -
let ?k=kernel let ?c=part2rel let ?d=Domain let ?r=Range
have "?c (?k R) = 
\<Union> ((% x . (x \<times> x)) ` {R^-1 `` {y}| y::'b. y\<in> ?r R})" using ll65 part2rel_def by metis
(*also have "... = \<Union> {R^-1``{y} \<times> (R^-1``{y})| y. y \<in> ?r R}" by auto
also have "... = 
{(x1, x2)|x1 x2 . EX y. (y \<in> (?r R) & x1 \<in> R^-1``{y} & x2 \<in> R^-1``{y})}" by blast
also have "... = 
{(x1, x2)|x1 x2 . EX y. (x1 \<in> R^-1``{y} & x2 \<in> R^-1``{y})}" by blast
 also have "... = {(x1, x2)|x1 x2 . EX y. {x1,x2} \<subseteq> R^-1``{y}}" by force*)
then show ?thesis by auto
qed

lemma ll03: shows "(part2rel (kernel R)) =  R O (R^-1)" using ll01 by auto

corollary ll05: assumes "runiq f" shows 
"f O (projector (f^-1)) = projector (part2rel (kernel f))"
using assms ll03 ll04 by metis

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

lemma ll16: shows "(P +* Q) outside (Domain Q) \<supseteq> P outside (Domain Q)" 
using assms paste_def Outside_def l38 l37 ll51 by (smt Un_commute Un_upper2)

lemma ll17: shows "Domain (P outside (X \<union> Domain P)) \<subseteq> {}" 
by (metis Diff_subset_conv Un_upper2 le_supI1 outside_reduces_domain)

lemma ll18: shows "P outside (X \<union> Domain P)={}" using ll17 by fast

lemma ll19: shows "(P +* Q) outside (X \<union> Domain Q) = 
P outside (X \<union> Domain Q)" using assms paste_def ll51 ll52 ll18 
(* by (metis outside_union_restrict restrict_empty sup.right_idem)*)
by (metis (hide_lams, no_types) empty_subsetI le_sup_iff subset_refl sup_absorb1 sup_absorb2)

lemma ll10: shows "trivial {x}" by (metis order_refl the_elem_eq trivial_def)

lemma ll11: assumes "trivial X" "{x} \<subseteq> X" shows "{x}=X" 
using singleton_sub_trivial_uniq assms by (metis subset_antisym trivial_def)

lemma ll12: fixes f::"('a \<times> 'b) set" assumes "runiq f" shows 
"Range (projector (f^-1)) = Range (projector (part2rel (kernel f)))"
(is "?A=?B")
proof -
(*TODO@MC: modularize & clean this proof *)
let ?r=Range let ?d=Domain let ?pp=projector let ?cc=part2rel let ?kk=kernel
let ?k="%R. {R^-1 `` {y}| y. y\<in> ?r R}"
let ?p="%R. {(x,R``{x})|x. x \<in> Domain R}"
let ?c="%X. \<Union> ((% x . (x \<times> x)) ` X)"
let ?ck="%R. {(x1, x2)|x1 x2 . EX y. {x1,x2} \<subseteq> R^-1``{y}}"
let ?if="f^-1"
let ?RH="{(x, f^-1``(f``{x}))| x::'a. x\<in>?d f}"
let ?LH="{(y, f^-1``{y})|y. y\<in> ?r f}"
let ?L="{f^-1``{y}|y. y\<in> ?r f}"
let ?R="{f^-1``(f``{x})|x. x\<in>?d f}"
have "?L={f^-1``z|z. EX y. y\<in>?r f & z={y}}" by auto
moreover have "...={f^-1``zz|zz. zz\<in>{z. EX y. y\<in>?r f & z={y}}}" by auto
ultimately have
11: "?L={f^-1``zz|zz. zz\<in>{z. EX y. y\<in>?r f & z={y}}}" by presburger
have "?R={f^-1``z|z. EX x. x\<in>?d f & z=f``{x}}" by blast
moreover have "...={f^-1``zz|zz. zz\<in>{z. EX x. x\<in>?d f & z=f``{x}}}" by auto
ultimately have
12: "?R={f^-1``zz|zz. zz\<in>{z. EX x. x\<in>?d f & z=f``{x}}}" by presburger
have 
2: "\<forall>y. (y\<in>?r f \<longleftrightarrow> (EX x.(x\<in>?d f & {y} \<subseteq> f``{x})))" using assms 
by auto
moreover have 
3: "\<forall>x y. {y} \<subseteq> f``{x} \<longrightarrow> {y}=f``{x}" using assms runiq_def ll10 ll11 by metis
ultimately have 
"\<forall>y. (y\<in>?r f \<longleftrightarrow> (EX x.(x\<in>?d f & {y} = f``{x})))" by blast
then have "{z. EX y. y\<in>?r f & z={y}} = 
{z. EX x y. x\<in>?d f & y\<in>?r f & z={y} & {y}=f``{x}}" by auto
moreover have "... = {z. EX x y. x\<in>?d f & z = f``{x}}" using 3 by fast
moreover have "{z. EX x y. x\<in>?d f & z = f``{x}} = {z. EX x . x\<in>?d f & z = f``{x}}" 
by auto
ultimately have "{z. EX y. y\<in>?r f & z={y}}={z. EX x. x\<in>?d f & z=f``{x}}" by presburger
hence 
4: "?L=?R" using 11 12 by presburger have 
1: "?pp=?p" using  projector_def by metis
then have "?A=?r (?p ?if)" by (rule HOL.arg_cong)
moreover have "... = ?L" by auto ultimately have 
5: "?L=?A" by presburger
have "?kk=?k" using ll65 by metis
moreover have "?cc=?c" using part2rel_def by auto
ultimately have "?B=?r(?p (?c (?k f)))" using 1 by metis
moreover have "?ck f = (?c (?k f))" using ll01 by auto
moreover have "?R=?r (?p (?ck f))" by auto
ultimately have "?B=?R" by presburger
thus ?thesis using 4 5 by presburger
qed

lemma ll13: shows "Domain (projector R)=Domain R" 
proof -
let ?d=Domain let ?p="%R. {(x,R``{x})|x. x \<in> ?d R}"
have "?d (?p R)=?d R" by blast thus ?thesis using projector_def by metis
qed

lemma ll14: assumes "x\<in>Domain f" "runiq f" shows "f,,x \<in> Range f"
using assms by (metis Range_iff eval_runiq_rel)

lemma ll28: shows "Graph f,,x=f x"
proof -
let ?P="%xx. True" let ?G="{(x, f x)|x. ?P x}"
have "?P x" by fast then 
have "?G,,x = f x" by (rule l16)
thus ?thesis using Graph_def by metis
qed

lemma ll26: assumes "\<not> trivial X" "trivial T" shows "X-T \<noteq> {}"
using assms by (metis Diff_iff empty_iff subsetI trivial_subset)

corollary ll25: shows "(P +* Q) `` (Domain Q - X) = Q``(Domain Q - X)"
proof -
let ?d=Domain let ?D="?d Q" let ?R="P +* Q" 
have "?R``(?D \<inter> (?D - X))=Q``(?D \<inter> (?D - X))" using ll50 by metis
also have "?D - X=?D \<inter> (?D - X)" by fastforce
ultimately show ?thesis by auto
qed

lemma ll41: shows "Domain (R||X) = Domain R \<inter> X" using restrict_def by fastforce

lemma ll42: shows "Domain (R outside X)=Domain R - X" using Outside_def by blast

lemma ll40: assumes "trivial X" "trivial Y" shows "trivial (X \<times> Y)"
proof -
let ?e=the_elem let ?x="?e X" let ?y="?e Y" let ?Z="X \<times> Y"
have "X \<subseteq> {?x} & Y \<subseteq> {?y}" using assms trivial_def by metis
hence "?Z \<subseteq> {(?x,?y)}" by blast
thus ?thesis using trivial_subset trivial_singleton by metis
qed

lemma ll37: shows "runiq(graph X f) & Domain(graph X f)=X" 
proof -
let ?F="{(x, f x)|x. x\<in>X}"
have "runiq?F" using l14 by fast 
also have "Domain ?F=X" by blast
ultimately show ?thesis using graph_def by metis
qed

lemma ll34: shows "graph X f \<subseteq> (graph (X \<union> Y) f)"
proof -
let ?g="%X. {(x, f x)|x. x\<in>X}" have "?g X \<subseteq> ?g (X \<union> Y)" by blast
thus ?thesis using graph_def by metis
qed

lemma ll33: assumes "x \<in> X" shows "graph X f,,x=f x" 
proof -
let ?P="%xx. xx\<in>X" let ?g="{(x, f x)|x. ?P x}"
have "?P x" using assms by fast then have "?g,,x=f x" by (rule l16)
thus ?thesis using graph_def by metis
qed

definition runiqs where "runiqs={f. runiq f}"

definition functional where "functional X = (\<forall>x \<in> X. runiq x)"
(*MC: Alternatively, say X \<subseteq> runiqs *)

definition cartesian where 
(*TODO@MC: make apply cartesian to Domain a, rather than to a itself 
Also consider moving i as an argument: cartesian i a = ...*) 
"cartesian X R x = (\<forall>y. (R+*({x}\<times>{y})\<in>X))"
(*
"cartesian a = (\<forall> b i y. ((b \<in> Domain a 
& i \<in> Domain b)
(*& Domain b = Domain bb*)
\<longrightarrow> b +* ({i} \<times> {y}) \<in> Domain a))"
*)

lemma ll38: assumes "runiq f" shows "cartesian runiqs f x"
proof -
  let ?U=runiqs let ?u=runiq let ?g=graph let ?c=cartesian
  {
    fix y::'b have "?u (f+*({x}\<times>{y}))"  
    using assms runiq_singleton_rel runiq_paste2 by fastforce
    hence "f +* ({x}\<times>{y})\<in>?U" using runiqs_def by fast
  }
  thus ?thesis using cartesian_def by fast
qed

corollary ll39: assumes "runiq f" shows "cartesian (Domain (graph runiqs F)) f x"
using ll38 ll37 assms by metis

lemma lll40: shows "(P \<union> Q) || X = (P || X) \<union> (Q||X)" using assms restrict_def 
proof -
let ?R="P \<union> Q" have "P \<inter> (X \<times> Range ?R) = P \<inter> (X \<times> Range P)" by blast moreover have 
"Q \<inter> (X \<times> Range ?R) = Q \<inter> (X \<times> Range Q)"by fast
ultimately show ?thesis using restrict_def by (metis inf_sup_aci(1) inf_sup_distrib2)
qed


lemma lll07: shows "(P \<inter> Q)``{x} = (P``{x} \<inter> (Q``{x}))" by fastforce

lemma assumes "P \<inter> Q={}" shows "P^-1 \<inter> Q^-1={}" using assms by fast

lemma lll00: shows "P||X = P outside (Domain P - X)" 
using Outside_def restrict_def by fastforce

lemma lll06a: shows "Domain (P outside X) \<inter> Domain (Q || X) \<subseteq> {}" using lll00 by 
(metis Diff_disjoint Domain_empty_iff Int_Diff inf_commute ll41 ll42 restrict_empty subset_empty)

lemma lll06b: shows "(P outside X) \<inter> (Q || X) = {}" using lll06a by fast

lemma lll11b: shows "P || (X \<inter> Y) \<subseteq> P||X & P outside (X \<union> Y) \<subseteq> P outside X" using 
Outside_def restrict_def Sigma_Un_distrib1 Un_upper1 inf_mono Diff_mono 
subset_refl by (metis (lifting) Sigma_mono inf_le1)

lemma lll06c: shows "(P outside (X \<union> Y)) \<inter> (Q || (X)) = {} & 
(P outside (X)) \<inter> (Q || (X \<inter> Z)) = {}
" using assms Outside_def restrict_def lll06b lll11b by fast

lemma lll11: shows "P || X \<subseteq> P||(X \<union> Y) & P outside X \<subseteq> P outside (X \<inter> Y)" 
using lll11b distrib_sup_le sup_idem inf_commute
by (smt le_inf_iff le_sup_iff subset_antisym sup.right_idem sup_commute)

lemma lll03: shows "P outside X \<subseteq> P outside (X \<inter> Domain P)" 
using Outside_def restrict_def lll11b by (smt Diff_Int Sigma_Int_distrib1 sup_ge1)

lemma lll01b: shows "P outside X \<subseteq> P || ((Domain P)-X)" 
using lll00 lll11 by (metis Int_commute ll41 outside_reduces_domain)

lemma lll01: shows "P outside X = P || (Domain P -X)" 
using Outside_def restrict_def  lll01b by fast

lemma lll02: shows "(P || X) || Y = P || (X \<inter> Y)" using lll00 ll52 
by (smt Int_commute Int_left_commute ll41 lll01 restriction_within_domain)

lemma lll04: shows "(P || X) outside Y = P || (X-Y)" using restrict_def
lll02 by (metis Diff_Compl double_complement ll42 lll00 lll01)

lemma lll06: shows "(P outside (X \<union> Y)) \<inter> (Q || (X \<inter> Z)) = {}" 
using lll06c by (metis (hide_lams, no_types) inf_commute lll02)



lemma lll71: shows "(P +* (Q::('a \<times> 'b) set)) || X = (P || X) +* (Q || X)"  
proof -
  let ?R="P+*Q" let ?d=Domain let ?dQ="?d Q" have 
  "?R || X = ((P outside ?dQ) || X) \<union> (Q || X)" using lll40 by (metis paste_def) moreover 
  have "(P outside ?dQ) || X = P ||(X - ?dQ)" using Outside_def restrict_def by (smt 
  Domain_Un_eq inf_sup_aci(5) ll52 lll00 lll04 outside_reduces_domain paste_Domain paste_def)
  moreover have "... = P || (X - (X \<inter> ?dQ))" by (metis Diff_Int_distrib Int_Diff Int_absorb)
  moreover have "... = (P || X) outside (X \<inter> ?dQ)" by (metis lll04)
  ultimately show ?thesis by (metis Int_commute ll41 paste_def)
qed

definition ler_in where "ler_in r= (\<Union>x. ({x} \<times> (r x -` {True})))"
(* inverts in_rel *)

lemma lll72: "(P +* Q) outside X = (P outside X) +* (Q outside X)" by (metis (hide_lams, no_types) 
Un_Diff_cancel Un_commute ll51 ll52 outside_reduces_domain paste_def)

lemma lll73: assumes "runiq f" shows "runiq (f +< (x,y))" using runiq_paste2 assms
runiq_singleton_rel by metis

lemma lll43: "(X2 \<times> {y}) outside X1 = (X2 - X1) \<times> {y}" using assms Outside_def 
by auto

lemma lll31: assumes "runiq P" shows "inj_on fst P" using assms 
runiq_def inj_on_def by (smt runiq_basic surjective_pairing)

lemma lll32: assumes "inj_on fst P" shows "runiq P" using assms 
inj_on_def by (metis (hide_lams, mono_tags) Pair_inject fst_conv runiq_basic)

lemma lll33: "runiq P=inj_on fst P" using lll31 lll32 by blast
(* Another characterization of runiq, reducing to lambda-functional injectivity *)

lemma lll34: assumes "runiq P" shows "card (Domain P) = card P" 
using assms lll33 card_image by (metis Domain_fst)

end

