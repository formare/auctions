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
where "F dummy Y n = \<Union> { set (injections_alg l Y) | l::'a list . size l = n \<and> distinct l }"
(* TODO CL: depending on why we need "card (set l) = n" it might be easier to simply say "distinct n". *)

text {* textbook-style definition of the set of all injective functions (represented as relations) from all sets
  of cardinality @{term n} to some other set *}
definition G :: "'a \<Rightarrow> 'b\<Colon>linorder set \<Rightarrow> nat \<Rightarrow> ('a\<Colon>linorder \<times> 'b) set set"
where "G dummy Y n = {f . finite (Domain f) \<and> card (Domain f) = n \<and> runiq f \<and> runiq (f\<inverse>) \<and> Range f \<subseteq> Y}"

(* CL: "case Nil" of RelationProperties.injections_equiv now covers this. *)
lemma ll43:
  fixes Y
  shows "F dummy Y 0 = {{}} \<and> G dummy Y 0 = {{}}"
proof
  have "injections_alg [] Y = [{}]" by auto
  then have "{{}} = \<Union> { set (injections_alg l Y) | l . size l = 0 \<and> distinct l }" by auto
  also have "\<dots> = F dummy Y 0" unfolding F_def by fast
  finally show "F dummy Y 0 = {{}}" by simp
next
  have "\<forall> f . finite (Domain f) \<and> card (Domain f) = 0 \<longrightarrow> f = {}" by force
  then have "\<forall> f. f \<in> G dummy Y 0 \<longrightarrow> f = {}" unfolding G_def by fast
  then have 0: "G dummy Y 0 \<subseteq> {{}}" by blast

  have 1: "finite (Domain {})" by simp
  have 2: "card (Domain {}) = 0" by force
  have 3: "runiq {}" using runiq_def trivial_def by fast
  moreover have "{}\<inverse> = {}" by fast
  ultimately have "runiq ({}\<inverse>)" by metis
  then have "{} \<in> G dummy Y 0" using 1 2 3 unfolding G_def by (smt Range_converse Range_empty `{}\<inverse> = {}` card_empty empty_subsetI finite.emptyI mem_Collect_eq)
  then show "G dummy Y 0 = {{}}" using 0 by auto
qed

lemma ll39:
  fixes n R
    and Y::"'b\<Colon>linorder set"
    and L::"'a list"
  assumes "\<forall> l::'a list. \<forall> r::('a \<times> 'b) set . size l = n \<and> r \<in> set (injections_alg l Y) \<longrightarrow> Domain r = set l"
      and size: "size L = Suc n"
      and R_inj: "R \<in> set (injections_alg L Y)"
  shows "Domain R = set L"
proof -
  let ?x = "hd L"
  let ?xs = "tl L"
  have "size L > 0" using size by simp
  then have 4: "L = ?x # ?xs" by fastforce
  then have "R \<in> set (injections_alg (?x # ?xs) Y)" using R_inj by auto
  then have "R \<in> set (concat [ sup_rels_from_alg RR ?x Y . RR \<leftarrow> injections_alg ?xs Y ])" 
    using assms(1) set_concat by force
  then obtain a where 
    0: "a \<in> set [ sup_rels_from_alg RR ?x Y . RR \<leftarrow> injections_alg ?xs Y ] \<and> R \<in> set a"
    using set_concat by fast
  then obtain r where 
    6: "a = sup_rels_from_alg r ?x Y \<and> r \<in> set (injections_alg ?xs Y)" by auto

  have "size ?xs = n" using size by auto
  then have 3: "Domain r = set ?xs" using 6 assms(1) by presburger
  have "R \<in> set [ r +* {(?x, y)} . y \<leftarrow> sorted_list_of_set (Y - Range r)]" 
    using 0 6 by force
  then obtain y where 
    2: "y \<in> set (sorted_list_of_set (Y - Range r)) \<and> R = r +* {(?x, y)}"
    using 0 6 set_concat assms(1) by auto
  then have "Domain R = Domain r \<union> {?x}" by (metis Domain_empty Domain_insert paste_Domain)
  also have "\<dots> = set ?xs \<union> {?x}" using 3 by presburger
  also have "\<dots> = insert ?x (set ?xs)" by fast
  also have "\<dots> = set L" using 4 by (metis List.set.simps(2))
  finally show ?thesis .
qed

lemma ll40:
  fixes Y::"'b\<Colon>linorder set"
    and n
    and x::'a
shows "\<forall> l . \<forall> r::('a \<times> 'b) set . size l = n \<and> r \<in> set (injections_alg l Y) \<longrightarrow> Domain r = set l" (is "?P n")
proof (induct n)
  case 0
  then show ?case by force
next
  case (Suc m)
  then show ?case using ll39 by blast
qed

lemma ll16:
  fixes l::"'a list"
    and Y::"'b\<Colon>linorder set"
    and R
  assumes "R \<in> set (injections_alg l Y)"
  shows "Domain R = set l"
using assms ll40 by blast

lemma ll42:
  fixes dummy Y n  
  assumes subset: "G dummy Y n \<subseteq> F dummy Y n"
      and finite: "finite Y"
  shows "G dummy Y (Suc n) \<subseteq> F dummy Y (Suc n)"
proof
  let ?F="F dummy Y" let ?G="G dummy Y" 
  fix g::"('a\<Colon>linorder \<times> 'b\<Colon>linorder) set"
  assume 0: "g \<in> G dummy Y (Suc n)"
  let ?lN="sorted_list_of_set (Domain g)" let ?x="hd ?lN" let ?xs="tl ?lN" 
  let ?Dn="Domain (g outside {?x})" 
  let ?Rn="Range (g outside {?x})" let ?e="\<lambda> z . (g outside {?x}) +* {(?x,z)}"
  have 6: "finite (Domain g) \<and> card (Domain g) = Suc n \<and> runiq g \<and> runiq (g\<inverse>) \<and> Range g \<subseteq> Y" 
    using 0 unfolding G_def by (rule CollectE)
  then have 61: "set ?lN= Domain g" by simp
  moreover have "?lN \<noteq> []"
    using 6 61
    by (metis Zero_not_Suc card_empty empty_set)
  ultimately have 7: "?x \<in> Domain g" by auto
  then have 8: "g ,, ?x \<in> g `` {?x}" using 6 Image_runiq_eq_eval by (metis insertI1)
  moreover have "(Domain g) \<inter> (Domain g - {?x}) \<inter> {?x} = {}" by fast
  then have "g `` (Domain g - {?x}) \<inter> (g `` {?x}) = {}" using 6 disj_Domain_imp_disj_Image by metis
  ultimately have "g ,, ?x \<notin> g `` (Domain g - {?x})" by blast
  then have "g ,, ?x \<notin> Range (g outside {?x})"
    using Range_def Outside_def Range_outside_sub_Image_Domain by blast
  then have 9: "g ,, ?x \<in> Y - Range (g outside {?x}) \<and> finite (Y - Range (g outside {?x}))"
    using 6 8 finite by blast
  have "g = (g outside {?x}) +* ({?x} \<times> g `` {?x})"
    using paste_outside_restrict restrict_to_singleton by metis
  also have "\<dots> = (g outside {?x}) +* ({?x} \<times> {g ,, ?x})"
    using 6 7 Image_runiq_eq_eval by metis
  also have "\<dots> = (g outside {?x}) +* {(?x, g ,, ?x)}" by simp
  ultimately have "g = ?e (g ,, ?x)" by presburger
  also have "g ,, ?x \<in> set (sorted_list_of_set (Y - Range (g outside {?x})))" 
    using 9 sorted_list_of_set by blast
  ultimately have "g \<in> set [?e z . z \<leftarrow> sorted_list_of_set (Y - Range (g outside {?x}))]" by auto
  then have 2: "g \<in> set (sup_rels_from_alg (g outside {?x}) ?x Y)" by simp
  have 22: "g outside {?x} \<subseteq> g" unfolding Outside_def by fast
  then have "(g outside {?x})\<inverse> \<subseteq> g\<inverse>" using converse_subrel by fast
  have 21: "card (Domain g) = Suc n \<and> runiq g \<and> runiq (g\<inverse>) \<and> Range g \<subseteq> Y" using 0 unfolding G_def by force
  then have 23: "finite (Domain g)" using card_ge_0_finite by force
  then have 24: "finite ?Dn" by (metis finite_Diff outside_reduces_domain)
  then have 25: "runiq (g outside {?x})" using subrel_runiq 21 22 by blast
  then have 26: "runiq ((g outside {?x})\<inverse>)" using subrel_runiq 22 converse_subrel 21 by metis
  then have 27: "?Dn = Domain g - {?x}" by (simp add: outside_reduces_domain)
  then have "?x \<in> Domain g" using 7 by force
  then have "card ?Dn = card (Domain g) - 1" using 27 23 by (simp add: card_Diff_singleton)
  then have "card ?Dn = n \<and> ?Rn \<subseteq> Range g" using 21 22 by auto
  then have "card ?Dn = n \<and> ?Rn \<subseteq> Y" using 21 by fast
  then have "g outside {?x} \<in> G dummy Y n" using 24 25 26 21 unfolding G_def by (metis (mono_tags) mem_Collect_eq)
  then have "g outside {?x} \<in> F dummy Y n" using subset by (simp add: in_mono)
  then obtain xs::"'a list"
    where 1: "g outside {?x} \<in> set (injections_alg xs Y) \<and> size xs = n \<and> distinct xs" unfolding F_def by blast
  let ?lN = "?x # xs"
  have 3: "size ?lN = Suc n" using 1 by simp 
  have "g \<in> set (concat [ sup_rels_from_alg R ?x Y . R \<leftarrow> injections_alg xs Y])" using 1 2 by auto
  then have 4: "g \<in> set (injections_alg (?x # xs) Y)" by auto
  then have 5: "card (set ?lN) = Suc n" using "21" by (metis ll16)
  then have 6: "distinct ?lN" using 3 4 by (metis card_distinct)
  then have "g \<in> ?F (Suc n)" unfolding F_def using 3 4 by blast
  also have "size ?lN = Suc n \<and> distinct ?lN" using 3 5 6 by fast
  ultimately show "g \<in> ?F (Suc n)" using F_def by blast
qed

lemma ll41:
  fixes dummy::"'a::linorder" 
    and Y::"'b::linorder set"
    and n::nat
  assumes finite: "finite Y"
      and subset: "F dummy Y n \<subseteq> G dummy Y n"
  shows "F dummy Y (Suc n) \<subseteq> G dummy Y (Suc n)"
proof
  let ?F = "F dummy Y" let ?G = "G dummy Y"
  let ?l="sorted_list_of_set"
  fix g assume "g \<in> F dummy Y (Suc n)" then 
  have "g \<in> \<Union> {set (injections_alg l Y) | l . size l= Suc n \<and> distinct l}" 
    unfolding F_def by fast
  then obtain a::"('a \<times> 'b) set set" where 
    0: "g \<in> a \<and> a \<in> {set (injections_alg l Y) | l . size l = Suc n \<and> distinct l}" 
    using F_def by blast
  obtain lN where
    1: "a = set (injections_alg lN Y) \<and> size lN = Suc n \<and> distinct lN" using 0 by blast  
  let ?x = "hd lN" let ?xs = "tl lN" have 
  20: "lN = ?x # ?xs" using 1 by (metis hd.simps length_Suc_conv tl.simps(2))
  have 21: "size ?xs=n" using 1 by auto
  then have 22: "distinct ?xs" using 1 by (metis distinct_tl)
  then have "set ?xs = set lN - {?x}" 
    using 1 20 by (metis (mono_tags) Diff_insert_absorb List.set.simps(2) distinct.simps(2))
  then have 2: "lN = ?x # ?xs \<and> size ?xs=n \<and> distinct ?xs \<and> set ?xs=set lN-{?x}" 
    using 20 21 22 by fast
  have "injections_alg (?x # ?xs) Y = concat [ sup_rels_from_alg R ?x Y . R <- injections_alg ?xs Y]" 
    by simp
  then have "set (injections_alg lN Y) = \<Union> {set l | l . l \<in> set [ sup_rels_from_alg R ?x Y. R <- injections_alg ?xs Y]}"
    using set_concat 2 by metis
  then obtain f where 
    3: "f \<in> set (injections_alg ?xs Y)" and 33: "g \<in> set (sup_rels_from_alg f ?x Y)"
    using 0 1 by fastforce
  have "set (injections_alg ?xs Y) \<in> {set (injections_alg l Y) | l . size l = n \<and> distinct l}"
    using 2 by fast
  then have "f \<in> ?F n" using 3 unfolding F_def by blast
  then have "f \<in> ?G n" using subset by blast
  then have 5: "finite (Domain f) \<and> card (Domain f)=n \<and> runiq f \<and> runiq (f\<inverse>) \<and> Range f \<subseteq> Y"
    unfolding G_def by fast
  have "g \<in> set [ f +* {(?x,y)} . y <- ?l (Y - Range f) ]" using 33 by simp
  then obtain y where 4: "g=f +* {(?x, y)} \<and> y \<in> set (?l (Y - Range f))" using 3 by auto
  have "finite (Y -Range f)" using finite by fast
  then have 6: "g=f +* {(?x, y)} \<and> y \<in> Y - Range f" 
    using 4 by simp
  then have 9: "runiq g" using runiq_paste2 5 runiq_singleton_rel by fast
  have "Domain f=set ?xs" using 3 by (rule ll16)
  then have 7: "?x \<notin> Domain f" using 2 by force
  then have 8: "runiq (g\<inverse>)" using runiq_converse_paste_singleton 5 6 by force
  have 10: "Range g \<subseteq> Range f \<union> {y}" using 6 by (metis Range_empty Range_insert paste_Range)
  (* simplify this using g=f \<union> {...} *)
  have "Domain g=Domain f \<union> {?x}" using 6 paste_Domain by (metis Domain_empty Domain_insert)
  then have "card (Domain g) = Suc n" using 7 5 by auto
  then have "card (Domain g) = Suc n \<and> finite (Domain g)" using card_ge_0_finite by force
  then show "g \<in> ?G (Suc n)" using 8 9 10 5 6 unfolding G_def by blast
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

end

