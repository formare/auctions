(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Author: Marco B. Caminati http://caminati.co.nr

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Sets of injections, partitions, allocations expressed as suitable subsets of the corresponding universes *}

theory Universes

imports 
"~~/src/HOL/Library/Code_Target_Nat"
StrictCombinatorialAuction (* MC: why is the position of this dep relevant? *)
MiscTools
"~~/src/HOL/Library/Indicator_Function"

begin

section {* Preliminary lemmas *}

lemma lm63: assumes "Y \<in> set (all_partitions_alg X)" shows "distinct Y"
using assms distinct_sorted_list_of_set all_partitions_alg_def all_partitions_paper_equiv_alg'
by metis

lemma lm65: assumes "finite G" shows "all_partitions G = set ` (set (all_partitions_alg G))"
using assms lm64 all_partitions_alg_def all_partitions_paper_equiv_alg
distinct_sorted_list_of_set image_set by metis























section {* Definitions of various subsets of @{term UNIV}. *}

abbreviation "isChoice R == \<forall>x. R``{x} \<subseteq> x"
abbreviation "dualOutside R Y == R - (Domain R \<times> Y)"
notation dualOutside (infix "|-" 75)
notation Outside (infix "-|" 75)

abbreviation "partitionsUniverse == {X. is_partition X}"
lemma "partitionsUniverse \<subseteq> Pow UNIV" by simp       
abbreviation "partitionValuedUniverse == \<Union> P \<in> partitionsUniverse. Pow (UNIV \<times> P)"
lemma "partitionValuedUniverse \<subseteq> Pow (UNIV \<times> (Pow UNIV))" by simp
abbreviation "injectionsUniverse == {R. (runiq R) & (runiq (R^-1))}"
abbreviation "allocationsUniverse == injectionsUniverse \<inter> partitionValuedUniverse"
abbreviation "totalRels X Y == {R. Domain R = X & Range R \<subseteq> Y}"
abbreviation "strictCovers G == Union -` {G}"
(*
abbreviation "partitionsUniverse' == {P-{{}}| P. \<Inter>P \<in> {\<Union>P,{}} }"
abbreviation "partitionsUniverse'' == {P-{{}}| P. \<forall> Q \<subseteq> P. \<Inter>Q \<in> {\<Union>Q,{}} }"
abbreviation "partitionsUniverse''' == {P-{{}}| P. \<forall> Q \<subseteq> P. (Q \<noteq> {} & card Q \<noteq> 1) \<longrightarrow> \<Inter>Q={}}"
abbreviation "partitionsUniverse'''' == {P-{{}}| P. \<forall> Q \<in> Pow P - {{}}. card Q \<noteq> 1 \<longrightarrow>  \<Inter>Q={} }"
abbreviation "partitionsUniverse''''' == {P-{{}}| P. \<forall> Q \<subseteq> P. card Q \<noteq> 1 \<longrightarrow> \<Inter>Q={}}"
*)

section {* Results about the sets defined in the previous section *}

lemma lm01a: "partitionsUniverse \<subseteq>  {P-{{}}| P. \<Inter>P \<in> {\<Union>P,{}}}" unfolding is_partition_def by auto
lemma lm04: assumes "!x1 : X. (x1 \<noteq> {} & (! x2 : X-{x1}. x1 \<inter> x2={}))" shows "is_partition X" 
unfolding is_partition_def using assms by fast
lemma lm72: assumes "\<forall>x \<in> X. t x \<in> x" shows "isChoice (graph X t)" using assms
by (metis Image_within_domain' empty_subsetI insert_subset ll33 ll37 runiq_wrt_eval_rel subset_trans)

lemma "R |- Y = (R^-1 -| Y)^-1" using Outside_def by auto
lemma lm24: "injections = injections'" using injections_def by (metis(no_types))
lemma lm25: "injections' X Y \<subseteq> injectionsUniverse" by fast
lemma lm25b: "injections X Y \<subseteq> injectionsUniverse" using injections_def by blast
lemma lm26: "injections' X Y = totalRels X Y \<inter> injectionsUniverse" by fastforce

lemma lm47: assumes "a \<in> possibleAllocationsRel N G" shows 
"a^-1 \<in> injections (Range a) N & Range a partitions G & Domain a \<subseteq> N" 
unfolding injections_def using assms all_partitions_def injections_def by fastforce

lemma lll80: assumes "is_partition XX" "YY \<subseteq> XX" shows "(XX - YY) partitions (\<Union> XX - \<Union> YY)"
using is_partition_of_def is_partition_def assms
proof -
  let ?xx="XX - YY" let ?X="\<Union> XX" let ?Y="\<Union> YY"
  let ?x="?X - ?Y"
  have "\<forall> y \<in> YY. \<forall> x\<in>?xx. y \<inter> x={}" using assms is_partition_def by (metis Diff_iff set_rev_mp)
  then have "\<Union> ?xx \<subseteq> ?x" using assms by blast
  then have "\<Union> ?xx = ?x" by blast
  moreover have "is_partition ?xx" using subset_is_partition by (metis Diff_subset assms(1))
  ultimately
  show ?thesis using is_partition_of_def by blast
qed

lemma lll81a: assumes "a \<in> possible_allocations_rel G N" shows
"runiq a & runiq (a\<inverse>) & (Domain a) partitions G & Range a \<subseteq> N" 
proof -
  obtain Y where
  0: "a \<in> injections Y N & Y \<in> all_partitions G" using assms possible_allocations_rel_def by auto
  show ?thesis using 0 injections_def all_partitions_def mem_Collect_eq by fastforce
qed

lemma lll81b: assumes "runiq a" "runiq (a\<inverse>)" "(Domain a) partitions G" "Range a \<subseteq> N"
shows "a \<in> possible_allocations_rel G N"
proof -
  have "a \<in> injections (Domain a) N" unfolding injections_def using assms(1) assms(2)  assms(4) by blast
  moreover have "Domain a \<in> all_partitions G" using assms(3) all_partitions_def by fast
  ultimately show ?thesis using assms(1) possible_allocations_rel_def by auto
qed

lemma lll81: "a \<in> possible_allocations_rel G N \<longleftrightarrow>
runiq a & runiq (a\<inverse>) & (Domain a) partitions G & Range a \<subseteq> N"
using lll81a lll81b by blast

corollary assumes "runiq (P^-1)" shows "Range (P outside X) \<inter> Range (P || X)={}"
using assms lll78 by (metis lll01 lll85)

lemma lm10: "possible_allocations_rel' G N \<subseteq> injectionsUniverse"
using assms by force

lemma lm09: "possible_allocations_rel G N \<subseteq> {a. Range a \<subseteq> N & Domain a \<in> all_partitions G}"
using assms possible_allocations_rel_def injections_def by fastforce

lemma lm11: "injections X Y = injections' X Y" using injections_def
by metis

lemma lm12: "all_partitions X = all_partitions' X" using all_partitions_def is_partition_of_def 
by auto

lemma lm13: "possible_allocations_rel' A B = possible_allocations_rel A B" (is "?A=?B")
proof -
  have "?B=\<Union> { injections Y B | Y . Y \<in> all_partitions A }"
  using possible_allocations_rel_def by auto 
  moreover have "... = ?A" using injections_def lm12 by metis
  ultimately show ?thesis by presburger
qed

lemma lm14: "possible_allocations_rel G N \<subseteq> injectionsUniverse \<inter> {a. Range a \<subseteq> N & Domain a \<in> all_partitions G}"
using assms lm09 lm10 possible_allocations_rel_def injections_def by fastforce

lemma lm15: "possible_allocations_rel G N \<supseteq> injectionsUniverse \<inter> {a. Domain a \<in> all_partitions G & Range a \<subseteq> N}"
using possible_allocations_rel_def injections_def by auto

lemma lm16: "converse ` injectionsUniverse = injectionsUniverse" by auto

lemma lm17: "possible_allocations_rel G N = injectionsUniverse \<inter> {a. Domain a \<in> all_partitions G & Range a \<subseteq> N}"
using lm14 lm15 by blast

lemma lm18: "converse`(A \<inter> B)=converse`A \<inter> (converse`B)" by force

lemma lm19: "possibleAllocationsRel N G = injectionsUniverse \<inter> {a. Domain a \<subseteq> N & Range a \<in> all_partitions G}"
proof -
  let ?A="possible_allocations_rel G N" let ?c=converse let ?I=injectionsUniverse 
  let ?P="all_partitions G" let ?d=Domain let ?r=Range
  have "?c`?A = (?c`?I) \<inter> ?c` ({a. ?r a \<subseteq> N & ?d a \<in> ?P})" using lm17 by fastforce
  moreover have "... = (?c`?I) \<inter> {aa. ?d aa \<subseteq> N & ?r aa \<in> ?P}" by fastforce
  moreover have "... = ?I \<inter> {aa. ?d aa \<subseteq> N & ?r aa \<in> ?P}" using lm16 by metis
  ultimately show ?thesis by presburger
qed

corollary lm19c: "a \<in> possibleAllocationsRel N G = 
(a \<in> injectionsUniverse & Domain a \<subseteq> N & Range a \<in> all_partitions G)" 
using lm19 Int_Collect Int_iff by (metis (lifting))

corollary lm19d: assumes "a \<in> possibleAllocationsRel N1 G" shows 
"a \<in> possibleAllocationsRel (N1 \<union> N2) G"
proof - 
have "Domain a \<subseteq> N1 \<union> N2" using assms(1) lm19c by (metis le_supI1) 
moreover have "a \<in> injectionsUniverse & Range a \<in> all_partitions G" 
using assms lm19c by blast ultimately show ?thesis using lm19c by blast 
qed

corollary lm19b: "possibleAllocationsRel N1 G \<subseteq> possibleAllocationsRel (N1 \<union> N2) G"
using lm19d by (metis subsetI)

lemma assumes "x\<noteq>{}" shows "is_partition {x}" unfolding is_partition_def using assms is_partition_def by force

lemma lm20d: assumes "\<Union> P1 \<inter> (\<Union> P2) = {}" "is_partition P1" "is_partition P2" "X \<in> P1 \<union> P2" "Y \<in> P1 \<union> P2"
"X \<inter> Y \<noteq> {}" shows "(X = Y)" unfolding is_partition_def using assms is_partition_def by fast

lemma lm20e: assumes "\<Union> P1 \<inter> (\<Union> P2) = {}" "is_partition P1" "is_partition P2" "X \<in> P1 \<union> P2" "Y \<in> P1 \<union> P2"
"(X = Y)" shows "X \<inter> Y \<noteq> {}" unfolding is_partition_def using assms is_partition_def by fast

lemma lm20: assumes "\<Union> P1 \<inter> (\<Union> P2) = {}" "is_partition P1" "is_partition P2"
shows "is_partition (P1 \<union> P2)" unfolding is_partition_def using assms lm20d lm20e by metis

lemma lm21: "Range Q \<union> (Range (P outside (Domain Q))) = Range (P +* Q)"
unfolding paste_def Range_Un_eq Un_commute by (metis(no_types))

lemma lll77c: assumes "a1 \<in> injectionsUniverse" "a2 \<in> injectionsUniverse" "Range a1 \<inter> (Range a2)={}"
"Domain a1 \<inter> (Domain a2) = {}" shows "a1 \<union> a2 \<in> injectionsUniverse" 
using assms disj_Un_runiq by (metis (no_types) Domain_converse converse_Un mem_Collect_eq)

lemma lm22: assumes "R \<in> partitionValuedUniverse" shows "is_partition (Range R)"
using assms 
proof -
  obtain P where
  0: "P \<in> partitionsUniverse & R \<subseteq> UNIV \<times> P" using assms by blast
  have "Range R \<subseteq> P" using 0 by fast
  then show ?thesis using 0 mem_Collect_eq subset_is_partition by (metis)
qed

lemma lm23: assumes "a1 \<in> allocationsUniverse" "a2 \<in> allocationsUniverse" "\<Union> (Range a1) \<inter> (\<Union> (Range a2))={}"
"Domain a1 \<inter> (Domain a2) = {}" shows "a1 \<union> a2 \<in> allocationsUniverse"
proof -
  let ?a="a1 \<union> a2" let ?b1="a1^-1" let ?b2="a2^-1" let ?r=Range let ?d=Domain
  let ?I=injectionsUniverse let ?P=partitionsUniverse let ?PV=partitionValuedUniverse let ?u=runiq
  let ?b="?a^-1" let ?p=is_partition
  have "?p (?r a1) & ?p (?r a2)" using assms lm22 by blast then
  moreover have "?p (?r a1 \<union> ?r a2)" using assms by (metis lm20)
  then moreover have "(?r a1 \<union> ?r a2) \<in> ?P" by simp
  moreover have "?r ?a = (?r a1 \<union> ?r a2)" using assms by fast
  ultimately moreover have "?p (?r ?a)" using lm20 assms by fastforce
  then moreover have "?a \<in> ?PV" using assms by fast
  moreover have "?r a1 \<inter> (?r a2) \<subseteq> Pow (\<Union> (?r a1) \<inter> (\<Union> (?r a2)))" by auto
  ultimately moreover have "{} \<notin> (?r a1) & {} \<notin> (?r a2)" using is_partition_def by (metis Int_empty_left)
  ultimately moreover have "?r a1 \<inter> (?r a2) = {}" using assms lm22 is_partition_def by auto
  ultimately moreover have "?a \<in> ?I" using lll77c assms by fastforce
  ultimately show ?thesis by blast
qed

lemma lm27: assumes "a \<in> injectionsUniverse" shows "a - b \<in> injectionsUniverse" using assms 
by (metis (lifting) Diff_subset converse_mono mem_Collect_eq subrel_runiq)

lemma lm30b: "{a. Domain a \<subseteq> N & Range a \<in> all_partitions G} =
(Range -` (all_partitions G)) \<inter> (Domain -`(Pow N))" 
by fastforce

lemma lm30: "possibleAllocationsRel N G = injectionsUniverse \<inter> ((Range -` (all_partitions G))
\<inter> (Domain -`(Pow N)))"
using lm19 lm30b by metis 

lemma lm28a: assumes "a \<in> possibleAllocationsRel N G" shows "(a^-1 \<in> injections (Range a) N & Range a \<in> all_partitions G)"
using assms 
by (metis (mono_tags, hide_lams) lm19c lm47)

lemma lm28c: assumes "a^-1 \<in> injections (Range a) N" "Range a \<in> all_partitions G" 
shows "a \<in> possibleAllocationsRel N G" using assms image_iff by fastforce

lemma lm28: "a \<in> possibleAllocationsRel N G = (a^-1 \<in> injections (Range a) N & Range a \<in> all_partitions G)"
using lm28a lm28c by metis

lemma lm28d: assumes "a \<in> possibleAllocationsRel N G" shows "(a \<in> injections (Domain a) (Range a) 
& Range a \<in> all_partitions G & Domain a \<subseteq> N)" using assms lm28a 
by (metis (erased, lifting) Domain_converse converse_converse injectionsI injections_def mem_Collect_eq order_refl)

lemma lm28e: assumes "a \<in> injections (Domain a) (Range a)" 
"Range a \<in> all_partitions G" "Domain a \<subseteq> N" shows "a \<in> possibleAllocationsRel N G" 
using assms mem_Collect_eq lm19c injections_def by (metis (erased, lifting))

lemma lm28b: "a \<in> possibleAllocationsRel N G = (a \<in> injections (Domain a) (Range a) 
& Range a \<in> all_partitions G & Domain a \<subseteq> N)" using lm28d lm28e by metis

lemma lm29: "possibleAllocationsRel N G \<supseteq> injectionsUniverse \<inter> (Range -` (all_partitions G))
\<inter> (Domain -`(Pow N))" using subsetI Int_assoc lm30
by metis (*MC: not used?*)

corollary lm31: "possibleAllocationsRel N G = injectionsUniverse \<inter> (Range -` (all_partitions G))
\<inter> (Domain -`(Pow N))" using lm30 Int_assoc by (metis)

lemma lm32: assumes "a \<in> partitionValuedUniverse" shows "a - b \<in> partitionValuedUniverse" 
using assms subset_is_partition by fast

lemma lm35: assumes "a \<in> allocationsUniverse" shows "a - b \<in> allocationsUniverse" using assms 
lm27 lm32 by auto

lemma lm33: assumes "a \<in> injectionsUniverse" shows "a \<in> injections (Domain a) (Range a)"
using assms by (metis (lifting) injectionsI mem_Collect_eq order_refl)

lemma lm34: assumes "a \<in> allocationsUniverse" shows "a \<in> possibleAllocationsRel (Domain a) (\<Union> (Range a))"
proof -
let ?r=Range let ?p=is_partition let ?P=all_partitions have "?p (?r a)" using 
assms lm22 Int_iff by blast then have "?r a \<in> ?P (\<Union> (?r a))" unfolding all_partitions_def 
using is_partition_of_def  mem_Collect_eq by (metis) then show ?thesis using 
assms IntI Int_lower1 equalityE lm19 mem_Collect_eq set_rev_mp by (metis (lifting, no_types))
qed

lemma lm36: "{X} \<in> partitionsUniverse = (X \<noteq> {})" using is_partition_def by fastforce

lemma lm36b: "{(x, X)} - {(x, {})} \<in> partitionValuedUniverse" using lm36 by auto

lemma "runiq {(x,X)}" 
by (metis runiq_singleton_rel)

lemma lm37: "{(x, X)} \<in> injectionsUniverse" unfolding runiq_basic using runiq_singleton_rel by blast

lemma lm38: "{(x,X)} - {(x,{})} \<in> allocationsUniverse" using lm36b lm37 lm27 Int_iff by (metis (no_types))

lemma assumes "is_partition Y" "X \<subseteq> Y" shows "is_partition X" using assms subset_is_partition
by (metis(no_types))

lemma lm41: assumes "is_partition PP" "is_partition (Union PP)" shows "is_partition (Union ` PP)"
proof -
let ?p=is_partition let ?U=Union let ?P2="?U PP" let ?P1="?U ` PP" have 
0: "\<forall> X\<in>?P1. \<forall> Y \<in> ?P1. (X \<inter> Y = {} \<longrightarrow> X \<noteq> Y)" using assms is_partition_def Int_absorb 
Int_empty_left UnionI Union_disjoint ex_in_conv imageE by (metis (hide_lams, no_types))
{
  fix X Y assume 
  2: "X \<in> ?P1 & Y\<in>?P1 & X \<noteq> Y"
  then obtain XX YY where 
  1: "X = ?U XX & Y=?U YY & XX\<in>PP & YY\<in>PP" by blast
  then have "XX \<subseteq> Union PP & YY \<subseteq> Union PP & XX \<inter> YY = {}" 
  using 2 1 is_partition_def assms(1) Sup_upper by metis
  then moreover have "\<forall> x\<in>XX. \<forall> y\<in>YY. x \<inter> y = {}" using 1 assms(2) is_partition_def 
by (metis IntI empty_iff subsetCE)
  ultimately have "X \<inter> Y={}" using assms 0 1 2 is_partition_def by auto
}
then show ?thesis using 0 is_partition_def by metis
qed

lemma lm43: assumes "a \<in> allocationsUniverse" shows 
"(a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allocationsUniverse & 
\<Union> (Range ((a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)"
proof -
  let ?d=Domain let ?r=Range let ?U=Union let ?p=is_partition let ?P=partitionsUniverse let ?u=runiq 
  let ?Xi="X \<union> {i}" let ?b="?Xi \<times> (?r a)" let ?a1="a - ?b" let ?Yi="a``?Xi" let ?Y="?U ?Yi" 
  let ?A2="{(i, ?Y)}" let ?a3="{(i,{})}" let ?a2="?A2 - ?a3" let ?aa1="a outside ?Xi" 
  let ?c="?a1 \<union> ?a2" let ?t1="?c \<in> allocationsUniverse" have 
  7: "?U(?r(?a1\<union>?a2))=?U(?r ?a1) \<union> (?U(?r ?a2))" by (metis Range_Un_eq Union_Un_distrib) have 
  5: "?U(?r a) \<subseteq> ?U(?r ?a1) \<union> ?U(a``?Xi) & ?U(?r ?a1) \<union> ?U(?r ?a2) \<subseteq> ?U(?r a)" by blast have
  1: "?u a & ?u (a^-1) & ?p (?r a) & ?r ?a1 \<subseteq> ?r a & ?Yi \<subseteq> ?r a" 
  using assms Int_iff lm22 mem_Collect_eq by auto then have 
  2: "?p (?r ?a1) & ?p ?Yi" using subset_is_partition by metis have 
  "?a1 \<in> allocationsUniverse & ?a2 \<in> allocationsUniverse" using lm38 assms(1) lm35 by fastforce then have 
  "(?a1 = {} \<or> ?a2 = {})\<longrightarrow> ?t1" using Un_empty_left by (metis (lifting, no_types) Un_absorb2 empty_subsetI) moreover have 
  "(?a1 = {} \<or> ?a2 = {})\<longrightarrow> ?U (?r a) = ?U (?r ?a1) \<union> ?U (?r ?a2)" by fast ultimately have 
  3: "(?a1 = {} \<or> ?a2 = {})\<longrightarrow> ?thesis" using 7 by presburger
  { 
    assume
    0: "?a1\<noteq>{} & ?a2\<noteq>{}" then have "?r ?a2\<supseteq>{?Y}" using Diff_cancel Range_insert empty_subsetI 
    insert_Diff_single insert_iff insert_subset by (metis (hide_lams, no_types)) then have 
    6: "?U (?r a) = ?U (?r ?a1) \<union> ?U (?r ?a2)" using 5 by blast
    have "?r ?a1 \<noteq> {} & ?r ?a2 \<noteq> {}" using 0 by auto
    moreover have "?r ?a1 \<subseteq> a``(?d ?a1)" using assms by blast
    moreover have "?Yi \<inter> (a``(?d a - ?Xi)) = {}" using assms 0 1 lm40
    by (metis Diff_disjoint)
    ultimately moreover have "?r ?a1 \<inter> ?Yi = {} & ?Yi \<noteq> {}" by blast
    ultimately moreover have "?p {?r ?a1, ?Yi}" unfolding is_partition_def using  
IntI Int_commute empty_iff insert_iff subsetI subset_empty by metis
    moreover have "?U {?r ?a1, ?Yi} \<subseteq> ?r a" by auto
    then moreover have "?p (?U {?r ?a1, ?Yi})" by (metis "1" Outside_def subset_is_partition)
    ultimately moreover have "?p (?U`{(?r ?a1), ?Yi})" using lm41 by fast
    moreover have "... = {?U (?r ?a1), ?Y}" by force
    ultimately moreover have "\<forall> x \<in> ?r ?a1. \<forall> y\<in>?Yi. x \<noteq> y" 
    using IntI empty_iff by metis
    ultimately moreover have "\<forall> x \<in> ?r ?a1. \<forall> y\<in>?Yi. x \<inter> y = {}" using 0 1 2 is_partition_def
    by (metis set_rev_mp)
    ultimately have "?U (?r ?a1) \<inter> ?Y = {}" using lm42 
proof -
  have "\<forall>v0. v0 \<in> Range (a - (X \<union> {i}) \<times> Range a) \<longrightarrow> (\<forall>v1. v1 \<in> a `` (X \<union> {i}) \<longrightarrow> v0 \<inter> v1 = {})" 
by (metis (no_types) `\<forall>x\<in>Range (a - (X \<union> {i}) \<times> Range a). \<forall>y\<in>a \`\` (X \<union> {i}). x \<inter> y = {}`) (* failed *)
  thus "\<Union>Range (a - (X \<union> {i}) \<times> Range a) \<inter> \<Union>(a `` (X \<union> {i})) = {}" by blast
qed then have 
    "?U (?r ?a1) \<inter> (?U (?r ?a2)) = {}" by blast
    moreover have "?d ?a1 \<inter> (?d ?a2) = {}" by blast
    moreover have "?a1 \<in> allocationsUniverse" using assms(1) lm35 by blast
    moreover have "?a2 \<in> allocationsUniverse" using lm38 by fastforce
    ultimately have "?a1 \<in> allocationsUniverse & 
    ?a2 \<in> allocationsUniverse &
    \<Union>Range ?a1 \<inter> \<Union>Range ?a2 = {} & Domain ?a1 \<inter> Domain ?a2 = {}" 
by blast then have 
?t1 using lm23 by auto       
    then have ?thesis using 6 7 by presburger
  }
  then show ?thesis using 3 by linarith
qed

lemma lm45: assumes "Domain a \<inter> X \<noteq> {}" "a \<in> allocationsUniverse" shows
"\<Union>(a``X) \<noteq> {}" (*MC: Should be stated in more general form *)
proof -
  let ?p=is_partition let ?r=Range
  have "?p (?r a)" using assms Int_iff lm22 by auto
  moreover have "a``X \<subseteq> ?r a" by fast
  ultimately have "?p (a``X)" using assms subset_is_partition by blast
  moreover have "a``X \<noteq> {}" using assms by fast
  ultimately show ?thesis by (metis Union_member all_not_in_conv no_empty_eq_class)
qed

corollary lm45b: assumes "Domain a \<inter> X \<noteq> {}" "a \<in> allocationsUniverse" shows 
"{\<Union>(a``(X\<union>{i}))}-{{}} = {\<Union>(a``(X\<union>{i}))}" using assms lm45 by fast

corollary lm43b: assumes "a \<in> allocationsUniverse" shows 
"(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> allocationsUniverse & 
\<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})))) = \<Union>(Range a)"
proof -
have "a - ((X\<union>{i})\<times>(Range a)) = a outside (X \<union> {i})" using Outside_def by metis
moreover have "(a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allocationsUniverse"
using assms lm43 by fastforce
moreover have "\<Union> (Range ((a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)"
using assms lm43 by (metis (no_types))
ultimately have
"(a outside (X\<union>{i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allocationsUniverse & 
\<Union> (Range ((a outside (X\<union>{i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)" by
presburger
moreover have "{(i, \<Union> (a``(X \<union> {i})))} - {(i,{})} = {i} \<times> ({\<Union> (a``(X\<union>{i}))} - {{}})" 
by fast
ultimately show ?thesis by auto
qed

corollary lm43c: assumes "a \<in> allocationsUniverse" "Domain a \<inter> X \<noteq> {}" shows 
"(a outside (X\<union>{i})) \<union> ({i}\<times>{\<Union>(a``(X\<union>{i}))}) \<in> allocationsUniverse & 
\<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>{\<Union>(a``(X\<union>{i}))}))) = \<Union>(Range a)"
using assms lm43b lm45b
proof -
let ?t1="(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> allocationsUniverse"
let ?t2="\<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})))) = \<Union>(Range a)"
have 
0: "a \<in> allocationsUniverse" using assms(1) by fast 
then have "?t1 & ?t2" using lm43b 
proof - 
(*MC: Isabelle cannot do elementary logic steps, only could make it work via this ugly proof found by sledgehammer *)
  have "a \<in> allocationsUniverse \<longrightarrow> a -| (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allocationsUniverse"
    using lm43b by fastforce
  hence "a -| (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allocationsUniverse"
    by (metis "0")
  thus "a -| (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allocationsUniverse \<and> \<Union>Range (a -| (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}})) = \<Union>Range a"
    using "0" by (metis (no_types) lm43b)
qed
moreover have 
1: "{\<Union>(a``(X\<union>{i}))}-{{}} = {\<Union>(a``(X\<union>{i}))}" using lm45 assms by fast
ultimately show ?thesis by auto
qed

abbreviation "condition1 b i == (\<forall> t t'. (trivial t & trivial t' & Union t \<subseteq> Union t') \<longrightarrow>
setsum b ({i}\<times>t) \<le> setsum b ({i}\<times>t'))" 
(*MC: try to restate this in terms of monotone (Complete_Partial_Order.thy) or other similar functions*)

abbreviation "condition1b b i == \<forall> X Y. setsum b ({i}\<times>{X}) \<le> setsum b ({i}\<times>{X \<union> Y})"

lemma lm46: assumes "condition1 b i" "runiq a" shows 
"setsum b ({i}\<times>((a outside X)``{i})) \<le> setsum b ({i}\<times>{\<Union>(a``(X\<union>{i}))})"
proof -
  let ?u=runiq let ?I="{i}" let ?R="a outside X" let ?U=Union let ?Xi="X \<union>?I"
  let ?t1="?R``?I" let ?t2="{?U (a``?Xi)}"
  have "?U (?R``?I) \<subseteq> ?U (?R``(X\<union>?I))" by blast
  moreover have "... \<subseteq> ?U (a``(X\<union>?I))" using Outside_def by blast
  ultimately have "?U (?R``?I) \<subseteq> ?U (a``(X\<union>?I))" by auto
  then have 
  0: "?U ?t1 \<subseteq> ?U ?t2" by auto
  have "?u a" using assms by fast 
  moreover have "?R \<subseteq> a" using Outside_def by blast ultimately
  have "?u ?R" using subrel_runiq by metis
  then have "trivial ?t1" by (metis runiq_alt)
  moreover have "trivial ?t2" by (metis trivial_singleton)
  ultimately show ?thesis using assms 0 by blast
qed

lemma lm48: "possibleAllocationsRel N G \<subseteq> injectionsUniverse" using  lm19 by fast

lemma lm49: "possibleAllocationsRel N G \<subseteq> partitionValuedUniverse"
using assms lm47 is_partition_of_def is_partition_def by blast

corollary lm50: "possibleAllocationsRel N G \<subseteq> allocationsUniverse" using lm48 lm49 
by (metis (lifting, mono_tags) inf.bounded_iff)

lemma mm45: assumes "XX \<in> partitionValuedUniverse" shows "{} \<notin> Range XX" using assms 
mem_Collect_eq no_empty_eq_class by auto
corollary mm45b: assumes "a \<in> possibleAllocationsRel N G" shows "{} \<notin> Range a" using assms mm45 
lm50 by blast
lemma mm63: assumes "a \<in> possibleAllocationsRel N G" shows "Range a \<subseteq> Pow G"
using assms lm47 is_partition_of_def by (metis subset_Pow_Union)
corollary mm63b: assumes "a \<in> possibleAllocationsRel N G" shows "Domain a \<subseteq> N & Range a \<subseteq> Pow G - {{}}" using
assms mm63 insert_Diff_single mm45b subset_insert lm47 by metis
corollary mm63c: assumes "a \<in> possibleAllocationsRel N G" shows "a \<subseteq> N \<times> (Pow G - {{}})" 
using assms mm63b by blast
corollary mm63e: "possibleAllocationsRel N G \<subseteq> Pow (N\<times>(Pow G-{{}}))" using mm63c by blast

lemma lm51: assumes  
"a \<in> possibleAllocationsRel N G" 
"i\<in>N-X" 
"Domain a \<inter> X \<noteq> {}" 
shows 
"a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))}) \<in> possibleAllocationsRel (N-X) (\<Union> (Range a))"
proof -
  let ?R="a outside X" let ?I="{i}" let ?U=Union let ?u=runiq let ?r=Range let ?d=Domain
  let ?aa="a outside (X \<union> {i}) \<union> ({i} \<times> {?U(a``(X\<union>{i}))})" have 
  1: "a \<in> allocationsUniverse" using assms(1) lm50  set_rev_mp by blast
  have "i \<notin> X" using assms by fast then have 
  2: "?d a - X \<union> {i} = ?d a \<union> {i} - X" by fast
  have "a \<in> allocationsUniverse" using 1 by fast moreover have "?d a \<inter> X \<noteq> {}" using assms by fast 
  ultimately have "?aa \<in> allocationsUniverse & ?U (?r ?aa) = ?U (?r a)" apply (rule lm43c) done
  then have "?aa \<in> possibleAllocationsRel (?d ?aa) (?U (?r a))"
using lm34 by (metis (lifting, mono_tags))
then have "?aa \<in> possibleAllocationsRel (?d ?aa \<union> (?d a - X \<union> {i}))  (?U (?r a))"
by (metis lm19d)
  moreover have "?d a - X \<union> {i} = ?d ?aa \<union> (?d a - X \<union> {i})" using Outside_def by auto
  ultimately have "?aa \<in> possibleAllocationsRel (?d a - X \<union> {i}) (?U (?r a))" by simp
  then have "?aa \<in> possibleAllocationsRel (?d a \<union> {i} - X) (?U (?r a))" using 2 by simp
  moreover have "?d a \<subseteq> N" using assms(1) lm19c by metis
  then moreover have "(?d a \<union> {i} - X) \<union> (N - X) = N - X" using assms by fast
  ultimately have "?aa \<in> possibleAllocationsRel (N - X) (?U (?r a))" using lm19b 
  by (metis (lifting, no_types) in_mono)
  then show ?thesis by fast
qed

lemma lm52: assumes 
"condition1 (b::_ => real) i" 
"a \<in> allocationsUniverse" 
"Domain a \<inter> X \<noteq> {}" 
"finite a" shows 
"setsum b (a outside X) \<le> setsum b (a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))}))"
proof -
  let ?R="a outside X" let ?I="{i}" let ?U=Union let ?u=runiq let ?r=Range let ?d=Domain
  let ?aa="a outside (X \<union> {i}) \<union> ({i} \<times> {?U(a``(X\<union>{i}))})"
  have "a \<in> injectionsUniverse" using assms by fast then have 
  0: "?u a" by simp
  moreover have "?R \<subseteq> a & ?R--i \<subseteq> a" using Outside_def by blast
  ultimately have "finite (?R -- i) & ?u (?R--i) & ?u ?R" using finite_subset subrel_runiq
  by (metis assms(4))
  then moreover have "trivial ({i}\<times>(?R``{i}))" using runiq_def 
  by (metis ll40 trivial_singleton)
  moreover have "\<forall>X. (?R -- i) \<inter> ({i}\<times>X)={}" using outside_reduces_domain by force
  ultimately have 
  1: "finite (?R--i) & finite ({i}\<times>(?R``{i})) & (?R -- i) \<inter> ({i}\<times>(?R``{i}))={} & 
  finite ({i} \<times> {?U(a``(X\<union>{i}))}) & (?R -- i) \<inter> ({i} \<times> {?U(a``(X\<union>{i}))})={}" 
  using Outside_def lm54 by fast 
  have "?R = (?R -- i) \<union> ({i}\<times>?R``{i})" by (metis l39)
  then have "setsum b ?R = setsum b (?R -- i) + setsum b ({i}\<times>(?R``{i}))" 
  using 1 setsum.union_disjoint by (metis (lifting) setsum.union_disjoint)
  moreover have "setsum b ({i}\<times>(?R``{i})) \<le> setsum b ({i}\<times>{?U(a``(X\<union>{i}))})" using lm46 
  assms(1) 0 by metis
  ultimately have "setsum b ?R \<le> setsum b (?R -- i) + setsum b ({i}\<times>{?U(a``(X\<union>{i}))})" by linarith
  moreover have "... = setsum b (?R -- i \<union> ({i} \<times> {?U(a``(X\<union>{i}))}))" 
  using 1 setsum.union_disjoint by auto
  moreover have "... = setsum b ?aa" by (metis ll52)
  ultimately show ?thesis by linarith
qed

lemma lm55: assumes "finite X" "XX \<in> all_partitions X" shows "finite XX" using 
all_partitions_def is_partition_of_def 
by (metis assms(1) assms(2) finite_UnionD mem_Collect_eq)

lemma lm58: assumes "finite N" "finite G" "a \<in> possibleAllocationsRel N G"
shows "finite a" using assms lm57 rev_finite_subset by (metis lm28b lm55)

lemma lm59: assumes "finite N" "finite G" shows "finite (possibleAllocationsRel N G)"
proof -
have "finite (Pow(N\<times>(Pow G-{{}})))" using assms finite_Pow_iff by blast
then show ?thesis using mm63e rev_finite_subset by (metis(no_types))
qed

corollary lm53: assumes "condition1 (b::_ => real) i" "a \<in> possibleAllocationsRel N G" "i\<in>N-X" 
"Domain a \<inter> X \<noteq> {}" "finite N" "finite G" shows
"Max ((setsum b)`(possibleAllocationsRel (N-X) G)) \<ge> setsum b (a outside X)"
proof -
let ?aa="a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))})"
have "condition1 (b::_ => real) i" using assms(1) by fast
moreover have "a \<in> allocationsUniverse" using assms(2) lm50 by blast
moreover have "Domain a \<inter> X \<noteq> {}" using assms(4) by auto
moreover have "finite a" using assms lm58 by metis ultimately have 
0: "setsum b (a outside X) \<le> setsum b ?aa" by (rule lm52)
have "?aa \<in> possibleAllocationsRel (N-X) (\<Union> (Range a))" using assms lm51 by metis
moreover have "\<Union> (Range a) = G" using assms lm47 is_partition_of_def by metis
ultimately have "setsum b ?aa \<in> (setsum b)`(possibleAllocationsRel (N-X) G)" by (metis imageI)
moreover have "finite ((setsum b)`(possibleAllocationsRel (N-X) G))" using assms lm59 assms(5,6)
by (metis finite_Diff finite_imageI)
ultimately have "setsum b ?aa \<le> Max ((setsum b)`(possibleAllocationsRel (N-X) G))" by auto
then show ?thesis using 0 by linarith
qed

lemma assumes "f \<in> partitionValuedUniverse" shows "{} \<notin> Range f" using assms by (metis lm22 no_empty_eq_class)

lemma mm33: assumes "finite XX" "\<forall>X \<in> XX. finite X" "is_partition XX" shows 
"card (\<Union> XX) = setsum card XX" using assms is_partition_def card_Union_disjoint by fast

corollary mm33b: assumes "XX partitions X" "finite X" "finite XX" shows 
"card (\<Union> XX) = setsum card XX" using assms mm33 by (metis is_partition_of_def lll41)

lemma setsum_Union_disjoint_4: assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A Int B = {}" 
shows "setsum f (Union C) = setsum (setsum f) C" using assms setsum.Union_disjoint by fastforce
(*MC: resumed this from Isabelle2013-2/HOL library after upgrading to 2014*)

corollary setsum_Union_disjoint_2: assumes "\<forall>x\<in>X. finite x" "is_partition X" shows 
"setsum f (\<Union> X) = setsum (setsum f) X" using assms setsum_Union_disjoint_4 is_partition_def by fast

corollary setsum_Union_disjoint_3: assumes "\<forall>x\<in>X. finite x" "X partitions XX" shows
"setsum f XX = setsum (setsum f) X" using assms by (metis is_partition_of_def setsum_Union_disjoint_2)

corollary setsum_associativity: assumes "finite x" "X partitions x" shows
"setsum f x = setsum (setsum f) X" using assms setsum_Union_disjoint_3 by (metis is_partition_of_def lll41)

lemma lm19e: assumes "a\<in>allocationsUniverse" "Domain a\<subseteq>N" "\<Union>Range a=G" shows 
"a \<in>possibleAllocationsRel N G" using assms lm19c lm34 by (metis (mono_tags, lifting))

corollary nn24a: "(allocationsUniverse\<inter>{a. Domain a\<subseteq>N & \<Union>Range a=G})\<subseteq>possibleAllocationsRel N G"
using lm19e by fastforce
corollary nn24f: "possibleAllocationsRel N G \<subseteq> {a. Domain a\<subseteq>N}" using lm47 by blast
corollary nn24g: "possibleAllocationsRel N G \<subseteq> {a. \<Union>Range a=G}" using is_partition_of_def lm47 mem_Collect_eq subsetI
by (metis(mono_tags))
corollary assumes "a \<in> possibleAllocationsRel N G" shows "\<Union> Range a = G" using assms 
by (metis is_partition_of_def lm47)
corollary nn24e: "
possibleAllocationsRel N G \<subseteq>  allocationsUniverse &
possibleAllocationsRel N G \<subseteq> {a. Domain a\<subseteq>N & \<Union>Range a=G}" using nn24f nn24g
conj_subset_def lm50 by (metis (no_types))

corollary nn24b: "possibleAllocationsRel N G \<subseteq> allocationsUniverse\<inter>{a. Domain a\<subseteq>N & \<Union>Range a=G}"
(is "?L \<subseteq> ?R1 \<inter> ?R2")
proof - have "?L \<subseteq> ?R1 & ?L \<subseteq> ?R2" by (rule nn24e) thus ?thesis by auto qed

corollary nn24: "possibleAllocationsRel N G = (allocationsUniverse\<inter>{a. Domain a\<subseteq>N & \<Union>Range a=G})" 
(is "?L = ?R") 
proof -
  have "?L \<subseteq> ?R" using nn24b by metis moreover have "?R \<subseteq> ?L" using nn24a by fast
  ultimately show ?thesis by force
qed

corollary nn24c: "b \<in> possibleAllocationsRel N G=(b\<in>allocationsUniverse& Domain b\<subseteq>N & \<Union>Range b = G)" 
using nn24 Int_Collect by (metis (mono_tags, lifting))

corollary lm35d: assumes "a \<in> allocationsUniverse" shows "a outside X \<in> allocationsUniverse" using assms Outside_def
by (metis (lifting, mono_tags) lm35)















(* MC: some bridging results (maybe to be moved to a separate file) *)


lemma "{{}::('a \<times> 'b) set} \<subseteq> injections (set []) Y" 
by (metis Domain_empty Range_empty converse_empty empty_set empty_subsetI injectionsI insert_subset runiq_emptyrel)
lemma lm84: "totalRels {} Y = {{}}" by fast
lemma lm85: "{} \<in> injectionsUniverse" 
by (metis CollectI converse_empty runiq_emptyrel)
lemma "injectionsUniverse \<inter> (totalRels {} Y)={{}}" using lm84 lm85 by fast

lemma lm60: assumes "runiq f" "x\<notin>Domain f" shows "{ f \<union> {(x, y)} | y . y \<in> A }\<subseteq>runiqs" 
unfolding paste_def runiqs_def
using assms runiq_basic by blast

lemma "converse \<circ> converse=id" 
by (metis (erased, hide_lams) DEADID.map_id comp_apply comp_id converse_converse fun.map_cong0)

lemma lm95: "converse ` (converse ` X)=X" by auto
lemma lm66: "runiq (f^-1) = (f \<in> converse`runiqs)" unfolding runiqs_def by auto
lemma lm68: assumes "runiq (f^-1)" "A\<inter>Range f={}" shows "converse ` { f \<union> {(x, y)} | y . y \<in> A }\<subseteq>runiqs" 
using assms lm60 by fast

lemma lm68b: assumes "f\<in>converse`runiqs" "A\<inter>Range f={}" shows 
"{f\<union>{(x, y)}| y. y \<in> A} \<subseteq> converse`runiqs" (is "?l \<subseteq> ?r")
proof -
  have "runiq (f^-1)" using assms(1) lm66 by blast then
  have "converse ` ?l \<subseteq> runiqs" using assms(2) by (rule lm68) 
  then have "?r \<supseteq> converse`(converse`?l)" by auto
  moreover have "converse`(converse`?l)=?l" by (rule lm95)
  ultimately show ?thesis by simp
qed

lemma lm67: "{ f \<union> {(x, y)} | y . y \<in> A } \<subseteq> totalRels ({x} \<union> Domain f) (A \<union> Range f)" by force

lemma lm69: "injectionsUniverse=runiqs\<inter>converse`runiqs" unfolding runiqs_def by auto

lemma lm73: assumes "f\<in>injectionsUniverse" "x\<notin>Domain f" "A\<inter>Range f={}" shows 
"{f \<union> {(x, y)}| y. y \<in> A} \<subseteq> injectionsUniverse" (is "?l \<subseteq> ?r") 
proof -  
have "f \<in> converse`runiqs" using assms(1) lm69 by blast
then have "?l \<subseteq> converse`runiqs" using assms(3) by (rule lm68b)
moreover have "?l \<subseteq> runiqs" using assms(1,2) lm60 by force 
ultimately show ?thesis using lm69 by blast
qed

lemma lm26b: "injections X Y = totalRels X Y \<inter> injectionsUniverse" using injections_def lm26 
by metis

lemma lm27b: assumes "f \<in> injectionsUniverse" shows "f outside A \<in> injectionsUniverse" using assms 
by (metis (no_types) Outside_def lm27)

lemma lm91: assumes "R \<in> totalRels A B" shows "R outside C \<in> totalRels (A-C) B" 
unfolding Outside_def
using assms by blast

lemma lm71: assumes "g \<in> injections' A B" shows "g outside C \<in> injections' (A-C) B" 
using assms Outside_def Range_outside_sub lm27 mem_Collect_eq outside_reduces_domain
by fastforce

lemma lm71b: assumes "g \<in> injections A B" shows "g outside C \<in> injections (A-C) B"
using assms lm71 by (metis injections_def)

lemma lm74: "{x}\<times>{y}={(x,y)}" by simp

lemma lm75: assumes "x\<in>Domain f" "runiq f" shows "{x}\<times>f``{x} = {(x,f,,x)}" 
using assms lm74 Image_runiq_eq_eval by metis

corollary lm92: assumes "x\<in>Domain f" "runiq f" shows "f=f -- x \<union> {(x,f,,x)}" using assms lm75 l39 by metis

lemma nn30b: assumes "f\<in>injectionsUniverse" shows "Range(f outside A) = Range f - f``A" 
using assms mem_Collect_eq nn30 by (metis)

lemma lm76: assumes "g\<in>injections' X Y" "x \<in> Domain g" shows "g\<in>{g--x \<union> {(x,y)}|y. y\<in>Y-Range (g--x)}" 
(* using assms lm72 Image_runiq_eq_eval  mem_Collect_eq DiffI Diff_disjoint eval_runiq_in_Range insert_disjoint(2) nn30 subsetD by smt2 *)
proof - let ?f="g--x" have "g\<in>injectionsUniverse" using assms(1) lm26 by fast then moreover have 
"g,,x \<in> g``{x}" using assms(2) by (metis Image_runiq_eq_eval insertI1 mem_Collect_eq)
ultimately have "g,,x \<in> Y-Range ?f" using nn30b assms(1) by fast moreover have "g=?f\<union>{(x, g,,x)}" 
using assms lm92 mem_Collect_eq by (metis (lifting)) ultimately show ?thesis by blast qed

corollary lm71c: assumes "x \<notin> X" "g \<in> injections ({x}\<union>X) Y" shows "g--x \<in> injections X Y" using assms lm71b by (metis Diff_insert_absorb insert_is_Un)

corollary lm77: assumes "x \<notin> X" "g \<in> injections ({x}\<union>X) Y" (is "g \<in> injections (?X) Y") shows 
"\<exists> f \<in> injections X Y. g \<in> {f\<union>{(x,y)}|y. y \<in> Y-Range f}" using assms lm71c lm76 
proof - 
  let ?f="g--x" have 1: "g\<in>injections' ?X Y" using assms Universes.lm24 by metis 
  have "Domain g=?X" using assms(2) Universes.lm24 mem_Collect_eq by (metis (mono_tags, lifting))
  then have 0: "x \<in> Domain g" by simp then have "?f \<in> injections X Y" using assms lm71c by fast
  moreover have "g\<in>{?f\<union>{(x,y)}|y. y\<in>Y-Range ?f}" using 1 0 by (rule lm76)
  ultimately show ?thesis by blast
qed

corollary lm77b: assumes "x \<notin> X" shows "injections ({x}\<union>X) Y \<subseteq> (\<Union> f\<in>injections X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f})"
using assms lm77 by fast

lemma lm73b: assumes "x \<notin> X" shows "(\<Union> f\<in>injections' X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f}) \<subseteq> injections' ({x}\<union>X) Y" using assms lm73 injections_def lm26b lm67 
proof -
{ fix f assume "f \<in> injections' X Y" then have 
0: "f \<in> injectionsUniverse & x \<notin> Domain f & Domain f = X & Range f \<subseteq> Y" using assms by fast 
then have "f \<in> injectionsUniverse" by fast moreover have "x \<notin> Domain f" using 0 by fast
moreover have 1: "(Y-Range f) \<inter> Range f = {}" by blast
ultimately have "{f \<union> {(x, y)} | y . y \<in> (Y-Range f)} \<subseteq> injectionsUniverse" by (rule lm73)
moreover have "{f \<union> {(x, y)} | y . y \<in> (Y-Range f)} \<subseteq> totalRels ({x} \<union> X) Y" using lm67 0 by force
ultimately have "{f \<union> {(x, y)} | y . y \<in> (Y-Range f)} \<subseteq> injectionsUniverse \<inter> totalRels ({x}\<union>X) Y" by auto}
thus ?thesis using lm26 by blast
qed

corollary lm78: assumes "x \<notin> X" shows 
"(\<Union> f\<in>injections X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f}) = injections ({x}\<union>X) Y" (is "?r=injections ?X _") 
proof - have 
0: "?r=(\<Union> f\<in>injections' X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f})" (is "_=?r'") unfolding Universes.lm24 by blast 
have "?r' \<subseteq> injections' ?X Y" using assms by (rule lm73b) moreover have "... = injections ?X Y" unfolding Universes.lm24 
by simp ultimately have "?r \<subseteq> injections ?X Y" using 0 by simp
moreover have "injections ?X Y \<subseteq> ?r" using assms by (rule lm77b) ultimately show ?thesis by blast
qed
lemma lm89: assumes "\<forall> x. (P x \<longrightarrow> (f x = g x))" shows "Union {f x|x. P x} = Union {g x | x. P x}" using assms try0
by blast
lemma lm88: assumes "x \<notin> Domain R" shows "R +* {(x,y)}=R\<union>{(x,y)}" using assms 
using paste_def by (metis (erased, lifting) Domain_empty Domain_insert Int_insert_right_if0 disjoint_iff_not_equal ex_in_conv paste_disj_domains)
lemma lm79: assumes "x \<notin> X" shows 
"(\<Union> f\<in>injections X Y. {f +* {(x, y)} | y . y \<in> Y-Range f}) = 
(\<Union> f\<in>injections X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f})" (is "?l = ?r") 
proof - have 
0: "\<forall>f \<in> injections X Y. x \<notin> Domain f" unfolding injections_def using assms by fast then have 
1: "?l=Union {{f +* {(x, y)} | y . y \<in> Y-Range f}|f .f \<in> injections X Y & x \<notin> Domain f}" 
(is "_=?l'") using assms by auto moreover have 
2: "?r=Union {{f \<union> {(x, y)} | y . y \<in> Y-Range f}|f .f \<in> injections X Y & x \<notin> Domain f}" 
(is "_=?r'") using assms 0 by auto have "\<forall> f. f\<in>injections X Y & x \<notin> Domain f \<longrightarrow> 
{f +* {(x, y)} | y . y \<in> Y-Range f}={f \<union> {(x, y)} | y . y \<in> Y-Range f}" using lm88 by force 
then have "?l'=?r'" by (rule lm89) then show "?l = ?r" using 1 2 by presburger
qed

corollary lm78b: assumes "x \<notin> X" shows 
"(\<Union> f\<in>injections X Y. {f +* {(x, y)} | y . y \<in> Y-Range f}) = injections ({x}\<union>X) Y" (is "?l=?r")
using assms lm78 
using lm79 
proof - have "?l=(\<Union> f\<in>injections X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f})" using assms by (rule lm79)
moreover have "... = ?r" using assms by (rule lm78) ultimately show ?thesis by presburger qed

lemma "set [G y. y <- l ] = {G y|y. y \<in> set l}" by auto
lemma "set (filter (%y. y \<notin> Range f) Y) = set Y - Range f" by auto
lemma lm81: "set [ f \<union> {(x,y)} . y \<leftarrow> (filter (%y. y \<notin> Range f) Y) ] = {f \<union> {(x,y)} | y . y \<in> (set Y)-Range f}" by auto
lemma lm82: assumes "\<forall>x\<in>set L. set (F x) = G x" shows "set (concat [ F x . x <- L]) = (\<Union> x\<in>set L. G x)"
using assms by force

lemma lm83: "set (concat [ [ f \<union> {(x,y)} . y \<leftarrow> (filter (%y. y \<notin> Range f) Y) ]. f \<leftarrow> F ])=
(\<Union> f\<in>set F. {f \<union> {(x,y)} | y . y \<in> (set Y)-Range f})" by auto
lemma lm81b: assumes "finite Y" shows "set [ f +* {(x,y)} . y \<leftarrow> sorted_list_of_set (Y - Range f) ] =
{f +* {(x,y)} | y . y \<in> Y-Range f}" 
using assms by auto
lemma lm83d: assumes "finite Y" shows "set (concat [ [ f +* {(x,y)} . y \<leftarrow> sorted_list_of_set (Y - Range f) ]. f \<leftarrow> F ]) = 
(\<Union> f\<in>set F. {f +* {(x,y)} | y . y \<in> Y-Range f})" using assms lm81b lm82 by auto

fun injectionsAlg where 
"injectionsAlg [] (Y::'a list) = [{}]" |
"injectionsAlg (x#xs) Y = concat [ 
   [R\<union>{(x,y)}. y \<leftarrow> (filter (%y. y \<notin> Range R) Y)]
   .R \<leftarrow> injectionsAlg xs Y ]"
abbreviation "possibleAllocationsAlg4 N G == 
map converse (concat [(injectionsAlg l N) . l \<leftarrow> all_partitions_list G])"

corollary lm83b: "set (injectionsAlg (x # xs) Y) = 
(\<Union> f\<in>set (injectionsAlg xs Y). {f \<union> {(x,y)} | y . y \<in> (set Y)-Range f})" using lm83 
injectionsAlg_def by auto

corollary lm83c: assumes "set (injectionsAlg xs Y)=injections (set xs) (set Y)" shows
"set (injectionsAlg (x # xs) Y) = 
(\<Union> f\<in>injections (set xs) (set Y). {f \<union> {(x,y)} | y . y \<in> (set Y)-Range f})" 
using assms lm83b by auto

text{* We sometimes use parallel @{term abbreviation} and @{term definition} for a same object to save typing `unfolding xxx' each time, as below: *}
lemma lm39: "injections' {} Y={{}}" by (simp add: lm26 lm84 runiq_emptyrel)
lemma lm39b: "injections {} Y={{}}" unfolding injections_def by (simp add: lm26 lm84 runiq_emptyrel) 

lemma lm80: "injectionsAlg [] Y=[{}]" using injectionsAlg_def by simp

lemma lm86: assumes "x \<notin> set xs" "set (injectionsAlg xs Y)=injections (set xs) (set Y)" shows
"set (injectionsAlg (x # xs) Y) = injections ({x}\<union>set xs) (set Y)" (is "?l=?r")
proof - 
have "?l = (\<Union> f\<in>injections (set xs) (set Y). {f \<union> {(x,y)} | y . y \<in> (set Y)-Range f})" 
using assms(2) by (rule lm83c) moreover have "... = ?r" using assms(1) by (rule lm78) 
ultimately show ?thesis by presburger
qed

lemma lm86b: assumes "x \<notin> set xs" "set (injections_alg xs Y)=injections (set xs) Y" "finite Y" shows
"set (injections_alg (x#xs) Y) = injections ({x}\<union>set xs) Y" (is "?l=?r")
proof - 
have "?l = (\<Union> f\<in>injections (set xs) Y. {f +* {(x,y)} | y . y \<in> Y-Range f})" 
using assms(2,3) lm83d by auto
moreover have "... = ?r" using assms(1) by (rule lm78b) 
ultimately show ?thesis by presburger
qed


corollary  assumes "distinct (x#xs)" 
"set (injectionsAlg xs Y)=injections (set xs) (set Y)" shows
"set (injectionsAlg (x # xs) Y) = injections ({x}\<union>set xs) (set Y)" 
using assms lm86 by (metis distinct.simps(2))

lemma listInduct: assumes "P []" "\<forall> xs x. P xs \<longrightarrow> P (x#xs)" shows "\<forall>x. P x"
using assms by (metis structInduct)
lemma lm01: "set (injections_alg [] Z)={{}}" by simp

theorem injections_equiv: assumes "finite Y" "distinct X" shows 
"set (injections_alg X Y)=injections (set X) Y"
proof -
let ?P="\<lambda> L. (distinct L \<longrightarrow> (set (injections_alg L Y)=injections (set L) Y))"
have "?P []" using assms by (metis Universes.lm01 list.set(1) lm39b) 
moreover have "\<forall>x xs. ?P xs \<longrightarrow> ?P (x#xs)" using assms lm86b by (metis distinct.simps(2) list.simps(15))
ultimately have "?P X" by (rule structInduct)
then show ?thesis using assms by presburger
qed

theorem assumes "distinct X" shows "set (injectionsAlg X Y)=injections (set X) (set Y)"
proof -
let ?P="\<lambda> L. (distinct L \<longrightarrow> (set (injectionsAlg L Y)=injections (set L) (set Y)))" 
have "?P []" by (simp add: Universes.lm24 lm39) 
moreover have "\<forall>x xs. ?P xs \<longrightarrow> ?P (x#xs)" by (metis distinct.simps(2) list.simps(15) lm86)
ultimately have "?P X" by (rule structInduct)
thus ?thesis using assms by presburger
qed


lemma assumes "R \<in> runiqs" shows "{ R +* {(x, y)} | y . y \<in> A }\<subseteq>runiqs" using assms 
by (smt2 Collect_mono inf_sup_ord(3) mem_Collect_eq outside_union_restrict paste_def runiq_paste1 runiq_singleton_rel runiqs_def subrel_runiq)














lemma assumes "Y \<in> set (all_partitions_alg G)" "card N > 0" "finite N" "finite G" 
shows "injections (set Y) N = set (injections_alg Y N)"
using assms injections_equiv lm63 by metis

lemma lm67: assumes "l \<in> set (all_partitions_list G)" "distinct G" shows "distinct l" 
using assms all_partitions_list_def by (metis all_partitions_paper_equiv_alg')
lemma lm68: assumes "card N > 0" "distinct G" shows 
"\<forall>l \<in> set (all_partitions_list G). set (injections_alg l N) = injections (set l) N"
using lm67 injections_equiv assms by blast

lemma lm69: assumes "card N > 0" "distinct G"
shows "{injections P N| P. P \<in> all_partitions (set G)} =
set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G]" using assms lm66 lm68 lm66b 
proof -
  let ?g1=all_partitions_list let ?f2=injections let ?g2=injections_alg
  have "\<forall>l \<in> set (?g1 G). set (?g2 l N) = ?f2 (set l) N" using assms lm68 by blast
  then have "set [set (?g2 l N). l <- ?g1 G] = {?f2 P N| P. P \<in> set (map set (?g1 G))}" apply (rule lm66) done
  moreover have "... = {?f2 P N| P. P \<in> all_partitions (set G)}" using all_partitions_paper_equiv_alg
  assms by blast
  ultimately show ?thesis by presburger
qed

lemma lm70: assumes "card N > 0" "distinct G" shows 
"Union {injections P N| P. P \<in> all_partitions (set G)} =
Union (set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G])" (is "Union ?L = Union ?R")
proof - have "?L = ?R" using assms by (rule lm69) thus ?thesis by presburger qed

corollary lm70b: assumes "card N > 0" "distinct G" shows 
"possibleAllocationsRel N (set G) = possibleAllocationsAlg2 N G" (is "?L = ?R") using assms lm70 
possible_allocations_rel_def 
proof -
  let ?LL="\<Union> {injections P N| P. P \<in> all_partitions (set G)}"
  let ?RR="\<Union> (set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G])"
  have "?LL = ?RR" using assms apply (rule lm70) done
  then have "converse ` ?LL = converse ` ?RR" by presburger
  thus ?thesis using possible_allocations_rel_def by force
qed




end

