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

theory b
(* MC@CL: Here, too, a lot stuff would fit good into Relation_Prop *)
imports a RelationProperties 

begin

lemma ll11: "P || X = P || (X \<inter> (Domain P))" 
proof -
let ?D="Domain P" let ?LH="P || X" let ?RH="P || (X \<inter> ?D)" let ?R="Range P"
(*have "?LH \<supseteq> ?RH" using restrict_def Domain_def ll26 
by (smt Int_lower1 Sigma_Int_distrib1 inf_mono order_refl)*)
have "P = P \<inter> (?D \<times> ?R)" by fast
hence "?LH = (P \<inter> (?D \<times> ?R)) \<inter> (X \<times> ?R)" using restrict_def by auto
also have "... = P \<inter> ((?D \<times> ?R) \<inter> (X \<times> ?R))" by blast
also have "... = P \<inter> ((?D \<inter> X) \<times> ?R)" by fast
also have "... = P || (X \<inter> ?D)" using restrict_def by fastforce
ultimately show "?LH = ?RH" by presburger
qed

lemma ll13: assumes "Domain P \<inter> (Domain Q)={}" shows "P +* Q = P \<union> Q"
using paste_subrel ll11 restrict_empty assms by (metis inf.commute inf_sup_ord(3) sup_bot_left)

lemma ll07: fixes X Y f F assumes "F = (%Z . ({ f z | z. z \<in> Z}))" 
shows "F (X \<union> Y) = F X \<union> (F Y)"
proof - (* pattern matching would be good here *)
let ?F="%Z . ({ f z | z. z \<in> Z})" let ?XY="X \<union> Y"
let ?LH="?F ?XY" let ?XX="?F X" let ?YY="?F Y" let ?RH="?XX \<union> ?YY"
have "?LH \<subseteq> ?RH" by fast also have "?RH \<subseteq> ?LH" by fast
ultimately show ?thesis using assms by fast
qed

lemma ll06: "inverse R = { (snd z, fst z) | z. z\<in>R }"
proof -
let ?LH="inverse R" let ?RH="{ (snd z, fst z)| z. z\<in>R}"
have "?LH \<subseteq> ?RH" using inverse_def snd_def fst_def by 
(smt Collect_cong equalityD2 prod.inject prod_caseE prod_caseI2 surjective_pairing)
also have "?LH \<supseteq> ?RH" using inverse_def snd_def fst_def by 
(smt Collect_cong Pair_inject equalityD2 prod_caseE prod_caseI2 surjective_pairing)
finally show ?thesis by fast
qed

lemma ll08: fixes P Q shows "inverse (P \<union> Q)=inverse P \<union> (inverse Q)"
proof -
let ?IP="inverse P" let ?IQ="inverse Q" let ?R="P \<union> Q" let ?LH="inverse ?R"
let ?RH="?IP \<union> ?IQ" 
have "?IP \<subseteq> ?LH" using ll06 by (smt in_mono inf_sup_ord(3) mem_Collect_eq subsetI)
also  have "?IQ \<subseteq> ?LH" using 
ll06 in_mono inf_sup_ord(3) mem_Collect_eq subsetI
by (smt sup_commute)
ultimately have "?RH \<subseteq> ?LH" by auto
also have "?LH \<subseteq> ?RH" using inverse_def ll06 by 
(smt Un_iff mem_Collect_eq subsetI sup.commute sup_commute)
finally show ?thesis by auto
qed

lemma ll25: fixes P Q assumes "P \<subseteq> Q" shows "inverse P \<subseteq> inverse Q"
using assms by (metis ll08 subset_Un_eq)

lemma ll01: fixes P Q assumes "runiq Q" assumes "runiq (P outside (Domain Q))" 
shows "runiq (P +* Q)"
proof - 
let ?dq="Domain Q" let ?PP="P outside ?dq" let ?R="P +* Q" let ?dpp="Domain ?PP"
let ?RR="?PP \<union> Q" have 
0: "?dpp \<inter> ?dq={}" using assms outside_reduces_domain by (metis Diff_Int2 Diff_Int_distrib2 Diff_cancel Int_Diff)
{
  fix a assume "a \<in> Domain ?RR"
  then have *: "trivial (?PP `` {a}) & trivial (Q `` {a})" using assms by (metis l18b runiq_def trivial_empty)
  then have "?PP `` {a}={} \<or> (Q `` {a}={})" using 0 by blast
  hence "?PP `` {a} = {} \<or> (Q `` {a} = {})" by fast
  hence "?RR `` {a} = Q `` {a} \<or> ?RR `` {a} = ?PP `` {a}" by blast
  hence "trivial (?RR `` {a})" using assms * by fastforce
}
hence "runiq ?RR" unfolding runiq_def by blast
thus ?thesis unfolding paste_def by simp
qed

lemma ll02: fixes x X assumes "trivial X" assumes "x \<subseteq> X" shows "trivial x"
using assms trivial_def by (metis (hide_lams, no_types) all_not_in_conv set_mp subsetI subset_singletonD)

corollary ll04: fixes P Q assumes "runiq Q" assumes "runiq P" 
shows "runiq (P +* Q)"
using ll01 subrel_runiq Outside_def by (metis Diff_subset assms(1) assms(2))

lemma ll05: "runiq {(x,y)}"
proof -
let ?f="%x . y" let ?P="% xx. xx=x" let ?X1="{(x,y)}" 
let ?X2="{(xx, ?f x) | xx. ?P xx}"
have "?X1 = ?X2" by auto also have "runiq ?X2" using l14 by fast
ultimately show ?thesis by presburger
qed

lemma assumes "trivial X" shows "runiq X"
using ll05 trivial_def by (metis assms subrel_runiq surj_pair)

lemma ll28: "P=(P outside X) +* (P || X)"
proof -
let ?p="P outside X" let ?q="P || X" let ?dp="Domain ?p" let ?dq="Domain ?q"
let ?D="Domain P" have "P \<subseteq> ?D \<times> (Range P)" by fast
hence "?p \<subseteq> ?D \<times> (Range P) - (X \<times> (Range P))" using Outside_def by (metis Diff_mono eq_refl)
hence "?dp \<subseteq> ?D - X" using Outside_def Domain_def by blast
also have "?dq=?D \<inter> X" using restrict_def by fastforce
ultimately have "?dp \<inter> ?dq = {}" by blast thus ?thesis using outside_union_restrict ll13 by metis
qed

lemma ll27: "set (concat LL)= \<Union> {set l | l . l \<in> set LL}"
proof -
let ?L="concat LL" let ?LH="set ?L" let ?X="{set l| l. l \<in> set LL}"
let ?RH="\<Union> ?X"
have "?LH \<supseteq> ?RH" using concat_def set_def by auto
also have "?LH \<subseteq> ?RH" using concat_def set_def by auto
finally show ?thesis by presburger
qed

lemma ll14: fixes f x assumes "runiq f" assumes "x \<notin> Domain f" 
shows "runiq (f +* {(x,y)})"
using assms ll04 ll05 by metis

lemma ll17: "Domain (P \<union> Q) = Domain P \<union> (Domain Q)"
by (metis Domain_Un_eq)

lemma ll20: "Domain (P +* Q) = (Domain P \<union> Domain Q)"
using ll17 outside_reduces_domain paste_def by (metis Un_Diff_cancel Un_commute)

lemma ll18: "P +* Q \<subseteq> P \<union> Q"
proof -
have "P outside (Domain Q) \<subseteq> P" using Outside_def by blast
also have "Q \<subseteq> Q" by fast
ultimately show ?thesis using paste_def by (metis (hide_lams, no_types) le_supI1 le_sup_iff sup_commute)
qed

lemma ll21: "Range (P +* Q) \<subseteq> Range P \<union> (Range Q)"
using ll18 by (metis Range_Un_eq Range_mono)

lemma ll30: fixes x f assumes "x \<in> Domain f" assumes "runiq f" 
shows "f `` {x} = {f ,, x}"
proof -
let ?X="{x}" let ?Y="f `` ?X" let ?y="f ,, x"
have "?Y \<subseteq> {?y}" using assms runiq_wrt_eval_rel by metis
also have "?y \<in> ?Y" using assms l25 by (metis Image_singleton_iff)
ultimately show ?thesis by blast
qed

lemma ll31: fixes X1 X2 R assumes "R `` X1 \<inter> (R `` X2) = {}" 
shows "Domain R \<inter> X1 \<inter> X2={}"
proof -
let ?Y1="R `` X1" let ?Y2="R `` X2" let ?D="Domain R" let ?X="X1 \<inter> X2"
have "R `` (?D \<inter> ?X) = R `` ?X" by fast also have "R `` ?X \<subseteq> ?Y1 \<inter> ?Y2" by blast
ultimately have 
1: "R `` (?D \<inter> ?X) \<subseteq> ?Y1 \<inter> ?Y2" by simp
{
  fix x assume 
  0: "x \<in> ?D \<inter> ?X" 
  hence "R `` {x} \<subseteq> R `` (?D \<inter> ?X)" by blast
  also have "R `` {x} \<noteq> {}" using 0 by fast
  ultimately have "?Y1 \<inter> ?Y2 \<noteq> {}" using 1 by force
}
thus ?thesis using assms Image_def by fast
qed

lemma ll36: "Domain (inverse R)=Range R"
using inverse_def ll06 Domain_def Range_def by auto

lemma ll38: "Range (R outside X) \<subseteq> R `` (Domain R - X)"
using Outside_def Image_def Domain_def Range_def by blast

lemma ll29: "P || {x} = {x} \<times> (P `` {x})"
proof -
let ?X="{x}" let ?LH="P||?X" let ?Y="P `` ?X" let ?RH="?X \<times> ?Y"
have "?RH \<subseteq> P" by fast
also have "Domain ?RH \<subseteq> ?X" by fast
finally have 0: "?RH \<subseteq> ?LH" using restrict_def by fast
have "Domain ?LH = Domain P \<inter> ?X" using restrict_def by fastforce
then also have "Range ?LH = ?Y" using restrict_def by fast
ultimately have "?LH \<subseteq> ?RH" by auto
thus ?thesis using 0 by fast
qed

lemma ll33: "Domain R \<inter> X \<subseteq> inverse R `` (R `` X)"
using inverse_def by fastforce

lemma ll34: fixes x f assumes  "runiq f" assumes "runiq (inverse f)"
assumes "x \<in> Domain f"
shows "inverse f `` ( f `` {x} ) = {x}"
proof -
let ?X="{x}" let ?Y="f `` ?X" let ?g="inverse f" let ?XX="?g `` ?Y" have 
0: "?X \<subseteq> ?XX" using ll33 assms by fast
have "trivial ?Y" using assms unfolding runiq_def by fast
hence "trivial ?XX" using assms runiq_wrt_eval_rel ll30 unfolding trivial_def by (metis RelationProperties.eval_rel.simps)
hence "?XX = ?X" using 0 trivial_def by (metis empty_iff insert_iff insert_subset order_refl subset_antisym)
thus ?thesis by auto
qed

lemma ll35: fixes x f assumes  "runiq f" assumes "runiq (inverse f)"
shows "inverse f `` ( f `` {x} ) \<subseteq> {x}"
using assms ll34 by (metis Image_empty eq_refl l18b subset_insertI)

lemma ll32: fixes X f assumes "runiq f" assumes "runiq (inverse f)"
shows "inverse f `` ( f `` X ) \<subseteq> X"
proof -
let ?g="inverse f" let ?Y="f `` X" let ?LH="?g `` ?Y" let ?I="f O ?g"
have "?I `` X = (\<Union>x \<in> X .?I `` {x})" 
using Image_def Image_eq_UN by blast
also have "... = (\<Union>x\<in>X. ?g `` (f `` {x}))" by blast
also have "... \<subseteq> (\<Union>x \<in> X. {x})" using ll35 assms by fast
also have "... = X" by simp
finally show ?thesis by fast
qed

lemma ll37: fixes X1 X2 f assumes "Domain f \<inter> X1 \<inter> X2 = {}" 
assumes "runiq f" assumes "runiq (inverse f)" shows 
"f `` X1 \<inter> (f `` X2)={}"
proof -
let ?g="inverse f" let ?Y1="f `` X1" let ?Y2="f `` X2" let ?D="Domain f"
let ?XX1="?D \<inter> X1" let ?XX2="?D \<inter> X2" have 
1: "?g `` (f `` ?XX1) \<subseteq> ?XX1" using ll32 assms by metis have 
2: "?g `` (f `` ?XX2) \<subseteq> ?XX2" using ll32 assms by metis hence 
4: "?g `` (f `` ?XX1) \<inter> (?g `` (f `` ?XX2)) \<subseteq> {}" using assms 1 by blast have 
3: "?XX1 \<inter> ?XX2 = {}" using assms by blast
hence "{} = Domain ?g \<inter> (f `` ?XX1) \<inter> (f `` ?XX2)" using ll31 4 by fast
also have "... = Range f \<inter> (f `` ?XX1) \<inter> (f `` ?XX2)" using ll36 by metis
also have "... = f `` ?XX1 \<inter> (f `` ?XX2)" by blast
finally show ?thesis by auto
qed

lemma ll15a: fixes P Q assumes "runiq (inverse P)" assumes "runiq (inverse Q)"
assumes "Domain P \<inter> (Domain Q)={}" assumes "Range P \<inter> (Range Q)={}"
shows "runiq (inverse (P +* Q))"
proof -
let ?i="inverse" let ?p="?i P" let ?q="?i Q" let ?R="P +* Q" let ?r="?i ?R"
have "?R = P \<union> Q" using assms ll13 by metis 
hence "?r = ?p \<union> ?q" using ll08 by auto
also have "... = ?p +* ?q" using assms ll13 ll36 by metis
ultimately show ?thesis using ll04 assms by auto
qed

lemma ll15: fixes R x assumes "runiq (inverse R)" 
assumes "y \<notin> Range R" assumes "x \<notin> Domain R"
shows "runiq (inverse (R +* {(x,y)}))"
proof -
have "inverse {(x,y)}={(y,x)}" using ll06 by auto then
have "runiq (inverse {(x,y)})" using ll05 by metis
also have "Domain R \<inter> Domain {(x,y)}={} & Range R \<inter> (Range {(x,y)})={}" 
using assms by blast ultimately show ?thesis using assms ll15a by blast
qed

definition childrenof 
(*::" ('a \<times> 'b::linorder) set => 'a => ('b set) => ('a \<times> 'b) set list"*)
where 
"childrenof R x Y = [ R +* {(x,y)} . y <- (sorted_list_of_set (Y - Range R))]"
(* Y or Y-Range R ? *)

fun bijections 
(*::"'a list => 'b::linorder set => ('a \<times> 'b) set list"*)
where
"bijections [] Y = [{}]" |
"bijections (x # xs) Y = concat [ childrenof R x Y . R <- bijections xs Y ]"

definition F
::"'a => ('b::linorder set) => nat => ('a::linorder \<times> 'b) set set"
where 
"F x Y n = \<Union> {set (bijections l Y) | l::('a list) . size l=n & card (set l)=n}"

definition G
::"'a => ('b::linorder set) => nat => ('a::linorder \<times> 'b) set set"
where 
"G x Y n = {f . 
finite (Domain f) & card (Domain f)=n & runiq f & runiq (inverse f) & Range f \<subseteq> Y}"

lemma ll43: fixes x Y shows "F x Y 0={{}} & G x Y 0={{}}"
proof -
(* fix x::"'a::linorder" fix Y::"'b::linorder set" fix n *)
let ?l="sorted_list_of_set" let ?B="bijections"
(* let ?F="%n. (\<Union> {set (bijections l Y) | l . size l=n & card (set l)=n})" *)
let ?F="F x Y"
(* let ?G="%n. {f . finite (Domain f) & card (Domain f)=n & runiq f & runiq (inverse f) & Range f \<subseteq> Y}" *)
let ?G="G x Y"
have "?B (?l {}) Y = [{}]" using bijections_def by auto
hence "{{}} = \<Union> {set (bijections l Y) | l . size l=0 & card (set l)=0}" by auto
also have "... = F x Y 0" using F_def by blast ultimately have
11: "F x Y 0={{}}" by force
have "\<forall> f . (finite (Domain f) & card (Domain f)=0 \<longrightarrow> f={})" by (metis Domain_empty_iff card_eq_0_iff)
hence "\<forall> f. (f \<in> ?G 0 \<longrightarrow> f={})" using G_def by fast
hence 0: "?G 0 \<subseteq> {{}}" by blast
have 1: "finite (Domain {})" by simp
have 2: "card (Domain {})=0" by force
have 3: "runiq {}" using runiq_def trivial_def by fast
also have "inverse {} = {}" using inverse_def by fast
ultimately have "runiq (inverse {})" by metis
hence "{} \<in> ?G 0" using G_def 1 2 3 by blast
hence "?G 0 = {{}}" using 0 by auto
hence "G x Y 0={{}}" using G_def by force
thus ?thesis using 11 by blast
qed

lemma ll39: fixes n R fixes Y::"'b::linorder set" fixes L::"'a list"
assumes "\<forall> l::('a list). \<forall> r::('a \<times> 'b) set . size l=n & r \<in> set (bijections l Y) \<longrightarrow> Domain r = set l"
assumes "size L=Suc n" assumes "R \<in> set (bijections L Y)"
shows "Domain R=set L"
proof -
let ?B="bijections" let ?c="childrenof" let ?l="sorted_list_of_set"
let ?ln="drop 1 L" let ?x="hd L" have "size L > 0" using assms by simp hence
4: "L=?x # ?ln" using assms by (metis One_nat_def drop_0 drop_Suc_conv_tl hd_drop_conv_nth)
hence "R \<in> set (?B (?x # ?ln) Y)" using assms by auto
hence "R \<in> set (concat [ ?c RR ?x Y . RR <- ?B ?ln Y ])" 
using assms bijections_def ll27 by fastforce
then obtain a where 
0: "a \<in> set [ ?c RR ?x Y . RR <- ?B ?ln Y ] & R \<in> set a" using ll27 by fast
obtain r where 
6: "a=?c r ?x Y & r \<in> set (?B ?ln Y)" using 0 by auto
have "size ?ln=n" using assms by auto then
have 3: "Domain r = set ?ln" using 6 assms by presburger
have "R \<in> set [ r +* {(?x, y)} . y <- ?l (Y - Range r)]" 
using 0 6 childrenof_def by metis then
obtain y where 
2: "y \<in> set (?l (Y - Range r)) & R=r +* {(?x, y)}" using 0 6 
ll27 childrenof_def assms by auto
have "Domain R=Domain r \<union> {?x}" using 2 by (metis Domain_empty Domain_insert ll20)
also have "... = set ?ln \<union> {?x}" using 3 by presburger
also have "... = insert ?x (set ?ln)" by fast
also have "... = set L" using 4 by (metis List.set.simps(2))
ultimately show ?thesis by presburger
qed

lemma ll40: fixes Y::"'b::linorder set" fixes n fixes x::'a
shows "\<forall> l . \<forall> r::(('a \<times> 'b) set) . size l=n & r \<in> set (bijections l Y) \<longrightarrow> Domain r=set l"
proof -
(* fix Y::"'b::linorder set" fix n::nat fix x::'a *)
let ?P="(%n::nat . (\<forall> l. \<forall> r::('a \<times> 'b) set . 
size l=n & r \<in> set (bijections l Y) \<longrightarrow> Domain r = set l))"
have "?P  n"
proof (rule nat.induct)
show "?P 0" by force
next
fix m assume "?P m" thus "?P (Suc m)" using ll39 by blast
qed
thus ?thesis by fast
qed

lemma ll16: fixes l::"'a list" fixes Y::"'b::linorder set" fixes R
assumes "R \<in> set (bijections l Y)" shows "Domain R = set l"
proof -
have "size l=size l & R \<in> set (bijections l Y)" using assms by fast
then show ?thesis using ll40 by blast
qed

lemma ll42: fixes x Y n assumes "G x Y n \<subseteq> F x Y n" 
assumes "finite Y" shows "G x Y (Suc n) \<subseteq> F x Y (Suc n)"
proof -
let ?B="bijections" let ?l="sorted_list_of_set" let ?c="childrenof"
let ?N="Suc n" let ?F="F x Y" let ?G="G x Y" 
let ?Fn="?F n" let ?Gn="?G n" let ?FN="?F ?N" let ?GN="?G ?N"
{
fix g
(* ::"('a::linorder \<times> 'b::linorder) set" *) 
assume
0: "g \<in> G x Y (Suc n)"
let ?DN="Domain g" let ?lN="?l ?DN" let ?x="hd ?lN" let ?ln="drop 1 ?lN" 
let ?f="g outside {?x}" let ?y="g ,, ?x" let ?RN="Range g" let ?Dn="Domain ?f" 
let ?Rn="Range ?f" let ?e="% z . (?f +* {(?x,z)})" have 
6: "finite ?DN & card ?DN=?N & runiq g & runiq (inverse g) & ?RN \<subseteq> Y" 
using 0 G_def by blast
hence "set ?lN=?DN" using sorted_list_of_set_def by simp
also have "?lN \<noteq> []" using 6 
by (metis Zero_not_Suc `set (sorted_list_of_set (Domain g)) = Domain g` card_empty empty_set)
ultimately have 
7: "?x \<in> ?DN" using 0 hd_in_set by metis hence 
8: "?y \<in> g `` {?x}" using 6 ll30 by (metis insertI1)
also have "?DN \<inter> (?DN - {?x}) \<inter> {?x} = {}" by fast
hence "g `` (?DN - {?x}) \<inter> (g `` {?x})={}" using 6 ll37 by metis
ultimately have "?y \<notin> g `` (?DN -{?x})" by blast
hence "?y \<notin> Range ?f" using Range_def Outside_def ll38 by blast hence 
9: "?y \<in> Y - Range ?f & finite (Y-Range ?f)" using 6 8 assms by blast
have "g = ?f +* ({?x} \<times> g `` {?x})" using ll28 ll29 by metis
also have "... = ?f +* ({?x} \<times> {?y})" using 6 7 ll30 by metis
also have "... = ?f +* {(?x, ?y)}" by simp
ultimately have "g = ?e ?y" by presburger
also have "?y \<in> set (?l (Y - Range ?f))" 
using 9 6 sorted_list_of_set assms by blast
ultimately have "g \<in> set [?e z . z <- ?l (Y - Range ?f)]" by auto hence 
2: "g \<in> set (childrenof ?f ?x Y)" using childrenof_def by metis have 
22: "?f \<subseteq> g" using Outside_def by (metis Diff_subset)
hence "inverse ?f \<subseteq> inverse g" using ll25 by metis
have
21: "card ?DN=?N & runiq g & runiq (inverse g) & ?RN \<subseteq> Y" using 0 G_def by blast hence 
23: "finite ?DN" using card_ge_0_finite by force hence 
24: "finite ?Dn" by (metis finite_Diff outside_reduces_domain) have 
25: "runiq ?f" using subrel_runiq Outside_def 21 by (metis Diff_subset) have 
26: "runiq (inverse ?f)" using subrel_runiq 22 ll25 21 by metis have 
27: "?Dn = ?DN - {?x}" by (metis outside_reduces_domain)
have "?x \<in> ?DN" using 23 sorted_list_of_set by (metis "21" Diff_empty Suc_diff_le Suc_eq_plus1_left add_diff_cancel_right' card_Diff_subset diff_le_self empty_set hd_in_set le_bot not_less_bot not_less_eq order_refl)
hence "card ?Dn=card ?DN - 1" using 27 card_Diff_singleton 23 by metis
hence "card ?Dn = n & ?Rn \<subseteq> ?RN" using 21 22 by auto
hence "card ?Dn = n & ?Rn \<subseteq> Y" using 21 by fast
hence "?f \<in> G x Y n" using 24 25 26 21 G_def by blast
hence "?f \<in> F x Y n" using assms by fast
then obtain ln::"'a list" where
1: "?f \<in> set (?B ln Y) & size ln=n & card (set ln)=n" using F_def by blast
let ?lN="?x # ln" have 
3: "size ?lN=?N" using 1 by (metis Suc_length_conv) 
have "g \<in> set (concat [ ?c R ?x Y . R <- ?B ln Y])" using 1 2 by auto hence 
4: "g \<in> set (?B (?x # ln) Y)" using bijections_def by auto
hence "card (set ?lN)=?N" using 1 by (metis "21" ll16)
hence "g\<in>?FN" using F_def 3 4 by blast
also have "size ?lN=?N & card (set ?lN)=?N" 
using 6 7 by (metis "3" `card (set (hd (sorted_list_of_set (Domain g)) # ln)) = Suc n`)
ultimately have "g \<in> ?FN" using F_def by blast
}
thus "?GN \<subseteq> ?FN" by force
qed

lemma ll41:
fixes x::"'a::linorder" 
fixes Y::"'b::linorder set"
fixes n::nat
assumes "finite Y"
assumes "F x Y n \<subseteq> G x Y n" shows "F x Y (Suc n) \<subseteq>
 G x Y (Suc n)"
proof -
let ?r="%x . runiq x" let ?F="F x Y" let ?G="G x Y" let ?B="bijections"
let ?c="childrenof" let ?l="sorted_list_of_set"
let ?Fn="?F n" let ?N="Suc n" let ?FN="?F ?N" let ?Gn="?G n" let ?GN="?G ?N"
{ 
  fix g assume "g \<in> F x Y (Suc n)" then 
  have "g \<in> \<Union> {set (?B l Y) | l . size l=(Suc n) & card (set l)=(Suc n)}" 
  using F_def by (metis (mono_tags))
  then obtain a::"('a \<times> 'b) set set" where 
  0: "g\<in> a & a\<in> {set (?B l Y) | l . size l=?N & card (set l)=?N}" 
  using F_def by blast
  obtain lN where
  1: "a=set (?B lN Y) & size lN=?N & card (set lN)=?N" using 0 by blast  
  let ?DN="set lN" 
  let ?x="hd lN" let ?ln="drop 1 lN" have 
  20: "lN=?x # ?ln" using 1 by (metis drop_1_Cons hd.simps length_Suc_conv)
  have 21: "size ?ln=n" using 1 by auto
  have 22: " card (set ?ln)=n" using 1 by 
  (metis `length (drop 1 lN) = n` distinct_drop distinct_imp_card_eq_length)
  have "set ?ln=set lN-{?x}" 
  using 1 by (smt Diff_insert_absorb List.set.simps(2) `card (set (drop 1 lN)) = n` `lN = hd lN # drop 1 lN` `length (drop 1 lN) = n` `\<And>thesis. (\<And>lN. a = set (bijections lN Y) \<and> length lN = Suc n \<and> card (set lN) = Suc n \<Longrightarrow> thesis) \<Longrightarrow> thesis` insert_absorb)
  hence
  2: "lN=?x # ?ln & size ?ln=n & card (set ?ln)=n & set ?ln=set lN-{?x}" 
  using 20 21 22 by fast
  have "?B (?x # ?ln) Y=concat [ ?c R ?x Y . R <- bijections ?ln Y]" 
  using bijections_def by auto
  hence "set (?B lN Y) = \<Union> {set l | l . l \<in> set [ ?c R ?x Y. R <- bijections ?ln Y]}"
  using ll27 2 by metis 
  then obtain f where 
  3: "f \<in> set (?B ?ln Y) & g \<in> set (?c f ?x Y)" using bijections_def 0 1 by auto
  let ?if="inverse f"
  have "set (?B ?ln Y) \<in> {set (bijections l Y) | l . size l=n & card (set l)=n}"
  using 2 by blast 
  hence "f \<in> ?Fn" using 2 3 F_def by fast
  hence "f \<in> ?Gn" using assms by blast hence 
  5: "finite (Domain f) & card (Domain f)=n & runiq f & runiq ?if & Range f \<subseteq> Y"
  using G_def by blast
  have "g \<in> set [ f +* {(?x,y)} . y <- ?l (Y - Range f) ]" using 3 childrenof_def by metis
  then obtain y where
  4: "g=f +* {(?x, y)} & y \<in> set (?l (Y - Range f))" using 3 childrenof_def by auto
  have "finite (Y -Range f)" using assms by fast hence
  6: "g=f +* {(?x, y)} & y \<in> Y - Range f" 
  using 4 sorted_list_of_set by metis hence 
  9: "runiq g" using ll04 5 ll05 by fast
  have "Domain f=set ?ln" using ll16 3 by blast hence 
  7: "?x \<notin> Domain f & card (Domain f)=n" using 2 by force hence 
  8: "runiq (inverse g)" using ll15 5 6 by force have 
  10: "Range g \<subseteq> Range f \<union> {y}" using 6 by (metis Range_empty Range_insert ll21)
  (* simplify this using g=f \<union> {...} *)
  have "Domain g=Domain f \<union> {?x}" using 6 ll20 by (metis Domain_empty Domain_insert)
  hence "card (Domain g)=?N" using 7 5 by auto
  hence "card (Domain g)=?N & finite (Domain g)" using card_ge_0_finite by force
  hence "g \<in> ?GN" using G_def 8 9 10 5 6 by fast
}
thus ?thesis by fast
qed

lemma ll44: fixes x Y n assumes "finite Y" shows "F x Y n \<subseteq> G x Y n"
proof (rule nat.induct)
show "F x Y 0 \<subseteq> G x Y 0" using ll43 by force
next
fix m assume "F x Y m \<subseteq> G x Y m"
thus "F x Y (Suc m) \<subseteq> G x Y (Suc m)" using ll41 assms by fast
qed

lemma ll45: fixes x Y n assumes "finite Y" shows "G x Y n \<subseteq> F x Y n"
proof (rule nat.induct)
show "G x Y 0 \<subseteq> F x Y 0" using ll43 by force
next
fix m assume "G x Y m \<subseteq> F x Y m"
thus "G x Y (Suc m) \<subseteq> F x Y (Suc m)" using ll42 assms by fast
qed

theorem fixes x Y assumes "finite Y" shows "G x Y=F x Y"
using assms ll44 ll45 by fast

(* CL@MC: could you please check whether the following are still needed, and delete them otherwise? *)
section {* unused leftovers *}

lemma ll22: assumes "finite X" shows "length (sorted_list_of_set X) = card X"
using assms by (metis distinct_card sorted_list_of_set)

end

