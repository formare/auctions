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
imports
  "../RelationProperties"
  "../ListUtils"

begin

(* TODO CL: see if we can get rid of the dummy arguments *)
text {* algorithmic definition of the set of all injective functions (represented as relations) from all sets 
  of cardinality @{term n} (represented as lists) to some other set *}
definition F :: "'a \<Rightarrow> 'b\<Colon>linorder set \<Rightarrow> nat \<Rightarrow> ('a\<Colon>linorder \<times> 'b) set set"
where "F dummy Y n = \<Union> {set (injections_alg l Y) | l::('a list) . size l=n & card (set l)=n}"

text {* textbook-style definition of the set of all injective functions (represented as relations) from all sets
  of cardinality @{term n} to some other set *}
definition G :: "'a \<Rightarrow> 'b\<Colon>linorder set \<Rightarrow> nat \<Rightarrow> ('a\<Colon>linorder \<times> 'b) set set"
where "G dummy Y n = {f . finite (Domain f) & card (Domain f)=n & runiq f & runiq (f\<inverse>) & Range f \<subseteq> Y}"

lemma ll43: fixes Y shows "F dummy Y 0 = {{}} \<and> G dummy Y 0 = {{}}"
proof -
(* fix x::"'a::linorder" fix Y::"'b::linorder set" fix n *)
let ?l="sorted_list_of_set" let ?B="injections_alg"
(* let ?F="%n. (\<Union> {set (bijections l Y) | l . size l=n & card (set l)=n})" *)
let ?F="F dummy Y"
(* let ?G="%n. {f . finite (Domain f) & card (Domain f)=n & runiq f & runiq (inverse f) & Range f \<subseteq> Y}" *)
let ?G="G dummy Y"
have "?B (?l {}) Y = [{}]" by auto
hence "{{}} = \<Union> {set (injections_alg l Y) | l . size l=0 & card (set l)=0}" by auto
also have "... = F dummy Y 0" unfolding F_def by fast
ultimately have
11: "F dummy Y 0 = {{}}" by simp
have "\<forall> f . (finite (Domain f) & card (Domain f)=0 \<longrightarrow> f={})" by (metis Domain_empty_iff card_eq_0_iff)
hence "\<forall> f. (f \<in> ?G 0 \<longrightarrow> f={})" unfolding G_def by (metis (lifting, full_types) mem_Collect_eq)
hence 0: "?G 0 \<subseteq> {{}}" by blast
have 1: "finite (Domain {})" by simp
have 2: "card (Domain {})=0" by force
have 3: "runiq {}" using runiq_def trivial_def by fast
also have "{}\<inverse> = {}" by fast
ultimately have "runiq ({}\<inverse>)" by metis
hence "{} \<in> ?G 0" using 1 2 3 unfolding G_def by (smt Range_converse Range_empty `{}\<inverse> = {}` card_empty empty_subsetI finite.emptyI mem_Collect_eq)
hence "?G 0 = {{}}" using 0 by auto
hence "G dummy Y 0={{}}" by fastforce
thus ?thesis using 11 by blast
qed

lemma ll39: fixes n R fixes Y::"'b::linorder set" fixes L::"'a list"
assumes "\<forall> l::('a list). \<forall> r::('a \<times> 'b) set . size l=n & r \<in> set (injections_alg l Y) \<longrightarrow> Domain r = set l"
assumes "size L=Suc n" assumes "R \<in> set (injections_alg L Y)"
shows "Domain R=set L"
proof -
let ?B="injections_alg" let ?c="sup_rels_from" let ?l="sorted_list_of_set"
let ?ln="drop 1 L" let ?x="hd L" have "size L > 0" using assms by simp hence
4: "L=?x # ?ln" using assms by (metis One_nat_def drop_0 drop_Suc_conv_tl hd_drop_conv_nth)
hence "R \<in> set (?B (?x # ?ln) Y)" using assms by auto
hence "R \<in> set (concat [ ?c RR ?x Y . RR <- ?B ?ln Y ])" 
using assms set_concat by force
then obtain a where 
0: "a \<in> set [ ?c RR ?x Y . RR <- ?B ?ln Y ] & R \<in> set a" using set_concat by fast
obtain r where 
6: "a=?c r ?x Y & r \<in> set (?B ?ln Y)" using 0 by auto
have "size ?ln=n" using assms by auto then
have 3: "Domain r = set ?ln" using 6 assms by presburger
have "R \<in> set [ r +* {(?x, y)} . y <- ?l (Y - Range r)]" 
using 0 6 by force then
obtain y where 
2: "y \<in> set (?l (Y - Range r)) & R=r +* {(?x, y)}" using 0 6 
set_concat assms by auto
have "Domain R=Domain r \<union> {?x}" using 2 by (metis Domain_empty Domain_insert paste_Domain)
also have "... = set ?ln \<union> {?x}" using 3 by presburger
also have "... = insert ?x (set ?ln)" by fast
also have "... = set L" using 4 by (metis List.set.simps(2))
ultimately show ?thesis by presburger
qed

lemma ll40: fixes Y::"'b::linorder set" fixes n fixes x::'a
shows "\<forall> l . \<forall> r::(('a \<times> 'b) set) . size l=n & r \<in> set (injections_alg l Y) \<longrightarrow> Domain r=set l"
proof -
(* fix Y::"'b::linorder set" fix n::nat fix x::'a *)
let ?P="(%n::nat . (\<forall> l. \<forall> r::('a \<times> 'b) set . 
size l=n & r \<in> set (injections_alg l Y) \<longrightarrow> Domain r = set l))"
have "?P  n"
proof (rule nat.induct)
show "?P 0" by force
next
fix m assume "?P m" thus "?P (Suc m)" using ll39 by blast
qed
thus ?thesis by fast
qed

lemma ll16: fixes l::"'a list" fixes Y::"'b::linorder set" fixes R
assumes "R \<in> set (injections_alg l Y)" shows "Domain R = set l"
proof -
have "size l=size l & R \<in> set (injections_alg l Y)" using assms by fast
then show ?thesis using ll40 by blast
qed

lemma ll42: fixes dummy Y n  
assumes "G dummy Y n \<subseteq> F dummy Y n"
and "finite Y"
shows "G dummy Y (Suc n) \<subseteq> F dummy Y (Suc n)"
proof -
let ?B="injections_alg" let ?l="sorted_list_of_set" let ?c="sup_rels_from"
let ?N="Suc n" let ?F="F dummy Y" let ?G="G dummy Y" 
let ?Fn="?F n" let ?Gn="?G n" let ?FN="?F ?N" let ?GN="?G ?N"
{
fix g
(* ::"('a::linorder \<times> 'b::linorder) set" *) 
assume
0: "g \<in> G dummy Y (Suc n)"
let ?DN="Domain g" let ?lN="?l ?DN" let ?x="hd ?lN" let ?ln="drop 1 ?lN" 
let ?f="g outside {?x}" let ?y="g ,, ?x" let ?RN="Range g" let ?Dn="Domain ?f" 
let ?Rn="Range ?f" let ?e="% z . (?f +* {(?x,z)})" have 
6: "finite ?DN & card ?DN=?N & runiq g & runiq (g\<inverse>) & ?RN \<subseteq> Y" 
using 0 unfolding G_def by (rule CollectE)
hence "set ?lN=?DN" using sorted_list_of_set_def by simp
also have "?lN \<noteq> []" using 6 
by (metis Zero_not_Suc `set (sorted_list_of_set (Domain g)) = Domain g` card_empty empty_set)
ultimately have 
7: "?x \<in> ?DN" using 0 hd_in_set by metis hence 
8: "?y \<in> g `` {?x}" using 6 Image_runiq_eq_eval by (metis insertI1)
also have "?DN \<inter> (?DN - {?x}) \<inter> {?x} = {}" by fast
hence "g `` (?DN - {?x}) \<inter> (g `` {?x})={}" using 6 disj_Domain_imp_disj_Image by metis
ultimately have "?y \<notin> g `` (?DN -{?x})" by blast
hence "?y \<notin> Range ?f" using Range_def Outside_def Range_outside_sub_Image_Domain by blast hence 
9: "?y \<in> Y - Range ?f & finite (Y-Range ?f)" using 6 8 assms by blast
have "g = ?f +* ({?x} \<times> g `` {?x})" using paste_outside_restrict restrict_to_singleton by metis
also have "... = ?f +* ({?x} \<times> {?y})" using 6 7 Image_runiq_eq_eval by metis
also have "... = ?f +* {(?x, ?y)}" by simp
ultimately have "g = ?e ?y" by presburger
also have "?y \<in> set (?l (Y - Range ?f))" 
using 9 6 sorted_list_of_set assms by blast
ultimately have "g \<in> set [?e z . z <- ?l (Y - Range ?f)]" by auto hence 
2: "g \<in> set (sup_rels_from ?f ?x Y)" by (metis sup_rels_from.simps) have 
22: "?f \<subseteq> g" using Outside_def by (metis Diff_subset)
hence "?f\<inverse> \<subseteq> g\<inverse>" using converse_subrel by metis
have
21: "card ?DN=?N & runiq g & runiq (g\<inverse>) & ?RN \<subseteq> Y" using 0 unfolding G_def by (metis "6")
hence 
23: "finite ?DN" using card_ge_0_finite by force hence 
24: "finite ?Dn" by (metis finite_Diff outside_reduces_domain) have 
25: "runiq ?f" using subrel_runiq Outside_def 21 by (metis Diff_subset) have 
26: "runiq (?f\<inverse>)" using subrel_runiq 22 converse_subrel 21 by metis have 
27: "?Dn = ?DN - {?x}" by (metis outside_reduces_domain)
have "?x \<in> ?DN" using 23 sorted_list_of_set by (metis "21" Diff_empty Suc_diff_le Suc_eq_plus1_left add_diff_cancel_right' card_Diff_subset diff_le_self empty_set hd_in_set le_bot not_less_bot not_less_eq order_refl)
hence "card ?Dn=card ?DN - 1" using 27 card_Diff_singleton 23 by metis
hence "card ?Dn = n & ?Rn \<subseteq> ?RN" using 21 22 by auto
hence "card ?Dn = n & ?Rn \<subseteq> Y" using 21 by fast
hence "?f \<in> G dummy Y n" using 24 25 26 21 unfolding G_def by (metis (mono_tags) mem_Collect_eq)
hence "?f \<in> F dummy Y n" using assms by (metis in_mono)
then obtain ln::"'a list" where
1: "?f \<in> set (?B ln Y) & size ln=n & card (set ln)=n" unfolding F_def by blast
let ?lN="?x # ln" have 
3: "size ?lN=?N" using 1 by (metis Suc_length_conv) 
have "g \<in> set (concat [ ?c R ?x Y . R <- ?B ln Y])" using 1 2 by auto hence 
4: "g \<in> set (?B (?x # ln) Y)" by auto
hence "card (set ?lN)=?N" using 1 by (metis "21" ll16)
hence "g\<in>?FN" using F_def 3 4 by blast
also have "size ?lN=?N & card (set ?lN)=?N" 
using 6 7 by (metis "3" `card (set (hd (sorted_list_of_set (Domain g)) # ln)) = Suc n`)
ultimately have "g \<in> ?FN" using F_def by blast
}
thus "?GN \<subseteq> ?FN" by force
qed

lemma ll41:
fixes dummy::"'a::linorder" 
fixes Y::"'b::linorder set"
fixes n::nat
assumes "finite Y"
assumes "F dummy Y n \<subseteq> G dummy Y n" shows "F dummy Y (Suc n) \<subseteq>
 G dummy Y (Suc n)"
proof -
let ?r="%x . runiq x" let ?F="F dummy Y" let ?G="G dummy Y" let ?B="injections_alg"
let ?c="sup_rels_from" let ?l="sorted_list_of_set"
let ?Fn="?F n" let ?N="Suc n" let ?FN="?F ?N" let ?Gn="?G n" let ?GN="?G ?N"
{ 
  fix g assume "g \<in> F dummy Y (Suc n)" then 
  have "g \<in> \<Union> {set (?B l Y) | l . size l=(Suc n) & card (set l)=(Suc n)}" 
  unfolding F_def by fast
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
  using 1 by (smt Diff_insert_absorb List.set.simps(2) `card (set (drop 1 lN)) = n` `lN = hd lN # drop 1 lN` `length (drop 1 lN) = n` `\<And>thesis. (\<And>lN. a = set (injections_alg lN Y) \<and> length lN = Suc n \<and> card (set lN) = Suc n \<Longrightarrow> thesis) \<Longrightarrow> thesis` insert_absorb)
  hence
  2: "lN=?x # ?ln & size ?ln=n & card (set ?ln)=n & set ?ln=set lN-{?x}" 
  using 20 21 22 by fast
  have "?B (?x # ?ln) Y=concat [ ?c R ?x Y . R <- injections_alg ?ln Y]" 
  by simp
  hence "set (?B lN Y) = \<Union> {set l | l . l \<in> set [ ?c R ?x Y. R <- injections_alg ?ln Y]}"
  using set_concat 2 by metis
  then obtain f where 
  3: "f \<in> set (?B ?ln Y) & g \<in> set (?c f ?x Y)" using 0 1 by fastforce
  let ?if="f\<inverse>"
  have "set (?B ?ln Y) \<in> {set (injections_alg l Y) | l . size l=n & card (set l)=n}"
  using 2 by blast 
  hence "f \<in> ?Fn" using 2 3 unfolding F_def by blast
  hence "f \<in> ?Gn" using assms by blast hence 
  5: "finite (Domain f) & card (Domain f)=n & runiq f & runiq ?if & Range f \<subseteq> Y"
  unfolding G_def by fast
  have "g \<in> set [ f +* {(?x,y)} . y <- ?l (Y - Range f) ]" using 3 by simp
  then obtain y where
  4: "g=f +* {(?x, y)} & y \<in> set (?l (Y - Range f))" using 3 by auto
  have "finite (Y -Range f)" using assms by fast hence
  6: "g=f +* {(?x, y)} & y \<in> Y - Range f" 
  using 4 sorted_list_of_set by metis hence 
  9: "runiq g" using runiq_paste2 5 runiq_singleton_rel by fast
  have "Domain f=set ?ln" using ll16 3 by blast hence 
  7: "?x \<notin> Domain f & card (Domain f)=n" using 2 by force hence 
  8: "runiq (g\<inverse>)" using runiq_converse_paste_singleton 5 6 by force have 
  10: "Range g \<subseteq> Range f \<union> {y}" using 6 by (metis Range_empty Range_insert paste_Range)
  (* simplify this using g=f \<union> {...} *)
  have "Domain g=Domain f \<union> {?x}" using 6 paste_Domain by (metis Domain_empty Domain_insert)
  hence "card (Domain g)=?N" using 7 5 by auto
  hence "card (Domain g)=?N & finite (Domain g)" using card_ge_0_finite by force
  hence "g \<in> ?GN" using 8 9 10 5 6 unfolding G_def by blast
}
thus ?thesis by fast
qed

theorem fixes Y assumes "finite Y" shows "G dummy Y=F dummy Y"
proof
  fix n
  show "G dummy Y n = F dummy Y n"
  (* 
  TODO CL: maybe change to first show \<subseteq>/\<supseteq>, then do induction in each case, because MC said:
  2) Proof-theoretically, having two separate induction steps to prove F
  c= G and G c= F supplies some information. It could be that to do the
  inductive step you need the (somehow) stronger assumption F(n)=G(n)
  --> F(n+1)=G(n+1).
  With the current proof, we know this is not the case.
  *)
  proof (induct n)
    case 0
    show ?case using ll43 by metis
  next
    case (Suc n)
    show ?case using assms ll41 ll42 Suc.hyps by (metis order_refl subset_antisym)
  qed
qed   

(* CL@MC: could you please check whether the following are still needed, and delete them otherwise? *)
section {* unused leftovers *}

lemma ll22: assumes "finite X" shows "length (sorted_list_of_set X) = card X"
using assms by (metis distinct_card sorted_list_of_set)

end

