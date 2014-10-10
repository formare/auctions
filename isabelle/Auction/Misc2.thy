theory Misc2

imports 
CombinatorialVickreyAuction
"~~/src/HOL/Library/Code_Target_Nat"
(* "../CombinatorialVickreyAuctionSoundness" *)
CombinatorialAuctionProperties
Relation
Misc1
"~~/src/HOL/Library/Indicator_Function"

begin

lemma lm63: assumes "Y \<in> set (all_partitions_alg X)" shows "distinct Y"
using assms distinct_sorted_list_of_set 
by (metis all_partitions_alg_def all_partitions_paper_equiv_alg')

lemma lm65: assumes "finite G" shows 
"all_partitions G = set ` (set (all_partitions_alg G))"
using lm64 all_partitions_alg_def all_partitions_paper_equiv_alg
by (metis assms distinct_sorted_list_of_set image_set)

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
"\<Union> {injections P N| P. P \<in> all_partitions (set G)} =
\<Union> (set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G])" using lm69 assms 
by (smt Collect_cong ex_map_conv map_ext)

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

abbreviation "isChoice R == \<forall>x. R``{x} \<subseteq> x"
abbreviation "dualOutside R Y == R - (Domain R \<times> Y)"
notation dualOutside (infix "|-" 75)
notation Outside (infix "-|" 75)

abbreviation "allPartitions == {X. is_partition X}"
lemma "allPartitions \<subseteq> Pow UNIV" by simp       
abbreviation "allPartitionvalued == \<Union> P \<in> allPartitions. Pow (UNIV \<times> P)"
lemma "allPartitionvalued \<subseteq> Pow (UNIV \<times> (Pow UNIV))" by simp
abbreviation "allInjections == {R. (runiq R) & (runiq (R^-1))}"
abbreviation "allocationsUniverse == allInjections \<inter> allPartitionvalued"
abbreviation "totalRels X Y == {R. Domain R = X & Range R \<subseteq> Y}"
abbreviation "strictCovers G == Union -` {G}"

lemma lm72: assumes "\<forall>x \<in> X. t x \<in> x" shows "isChoice (graph X t)" using assms
by (metis Image_within_domain' empty_subsetI insert_subset ll33 ll37 runiq_wrt_eval_rel subset_trans)

lemma "R |- Y = (R^-1 -| Y)^-1" using Outside_def by auto
lemma lm24: "injections' X Y = injections X Y" using injections_def by metis
lemma lm25: "injections' X Y \<subseteq> allInjections" by fast
lemma lm25b: "injections X Y \<subseteq> allInjections" using assms possible_allocations_rel_def 
injections_def all_partitions_def is_partition_of_def by blast
lemma lm26: "injections' X Y = totalRels X Y \<inter> allInjections" by fastforce

lemma lm47: fixes N fixes G fixes a assumes 
"a \<in> possibleAllocationsRel N G" shows 
"a^-1 \<in> injections (Range a) N & Range a partitions G & Domain a \<subseteq> N"
using assms all_partitions_def Domain_converse allocation_injective converse_converse 
image_iff injections_def mem_Collect_eq by smt

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
  show ?thesis using 0 injections_def by (smt all_partitions_def mem_Collect_eq)
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

lemma lm07: assumes "isChoice (graph {winningAllocationsRel N G b} t)" shows 
"t (winningAllocationsRel N G b) \<in> winningAllocationsRel N G b" 
using assms
proof - (* MC: to be cleaned *)
let ?W="winningAllocationsRel N G b" let ?T="graph {?W} t" let ?TT="graph UNIV t" let ?TTT="Graph t"
have "?T``{?W} \<subseteq> ?W" using assms by fast
moreover have "?TTT``{?W} = (?TTT || {?W})``{?W}" using restrict_def Image_def by fast
moreover have "?TTT || {?W} = ?TT || {?W}" using ll36 by metis
moreover have "... = ?T" using graph_def restrict_def Graph_def lm05 by (metis Int_UNIV_left)
moreover have "?T``{?W} = ?TTT``{?W}" using graph_def Graph_def by (metis calculation(2) lm06)
moreover have "?T``{?W} \<subseteq> t`{?W}" using l4 l5 ll36 by (metis calculation(5) subsetI)
ultimately show ?thesis using assms by (metis (hide_lams, no_types) image_eqI insertI1 l4 set_rev_mp)
qed

corollary lm03: "winningAllocationsRel N G b \<subseteq> possibleAllocationsRel N G" 
using assms lm02 by (smt mem_Collect_eq subsetI)

corollary assumes "runiq (P^-1)" shows "Range (P outside X) \<inter> Range (P || X)={}"
using assms lll78 by (metis lll01 lll85)

lemma lm10: "possible_allocations_rel' G N \<subseteq> allInjections"
using assms by force

lemma lm09: "possible_allocations_rel G N \<subseteq> {a. Range a \<subseteq> N & Domain a \<in> all_partitions G}"
using assms possible_allocations_rel_def injections_def by fastforce

lemma lm11: "injections X Y = injections' X Y" using injections_def
by metis

lemma lm12: "all_partitions X = all_partitions' X" using all_partitions_def is_partition_of_def 
by auto

lemma lm13: "possible_allocations_rel' A B = possible_allocations_rel A B" (is "?A=?B")
using possible_allocations_rel_def 
assms injections_def lm11 lm12 
proof -
  have "?B=\<Union> { injections Y B | Y . Y \<in> all_partitions A }"
  using possible_allocations_rel_def by auto 
  moreover have "... = ?A" using injections_def lm12 by metis
  ultimately show ?thesis by presburger
qed

lemma lm14: "possible_allocations_rel G N \<subseteq> allInjections \<inter> {a. Range a \<subseteq> N & Domain a \<in> all_partitions G}"
using assms lm09 lm10 possible_allocations_rel_def injections_def by fastforce

lemma lm15: "possible_allocations_rel G N \<supseteq> allInjections \<inter> {a. Domain a \<in> all_partitions G & Range a \<subseteq> N}"
using possible_allocations_rel_def injections_def by auto

lemma lm16: "converse ` allInjections = allInjections" by auto

lemma lm17: "possible_allocations_rel G N = allInjections \<inter> {a. Domain a \<in> all_partitions G & Range a \<subseteq> N}"
using lm14 lm15 by blast

lemma lm18: "converse`(A \<inter> B)=converse`A \<inter> (converse`B)" by force

lemma lm19: "possibleAllocationsRel N G = allInjections \<inter> {a. Domain a \<subseteq> N & Range a \<in> all_partitions G}"
using assms lm13 lm16 lm17 lm18 
proof -
  let ?A="possible_allocations_rel G N" let ?c=converse let ?I=allInjections 
  let ?P="all_partitions G" let ?d=Domain let ?r=Range
  have "?c`?A = (?c`?I) \<inter> ?c` ({a. ?r a \<subseteq> N & ?d a \<in> ?P})" using lm18 lm17 by fastforce
  moreover have "... = (?c`?I) \<inter> {aa. ?d aa \<subseteq> N & ?r aa \<in> ?P}" using lm16 by fastforce
  moreover have "... = ?I \<inter> {aa. ?d aa \<subseteq> N & ?r aa \<in> ?P}" using lm16 by metis
  ultimately show ?thesis by presburger
qed

corollary lm19c: "a \<in> possibleAllocationsRel N G = 
(a \<in> allInjections & Domain a \<subseteq> N & Range a \<in> all_partitions G)" using lm19 
by (metis (lifting) Int_Collect Int_iff)

corollary lm19b: "possibleAllocationsRel N1 G \<subseteq> possibleAllocationsRel (N1 \<union> N2) G"
using lm19c by (smt image_eqI image_subsetI sup.coboundedI2 sup_commute)

lemma lm20: assumes "\<Union> P1 \<inter> (\<Union> P2) = {}" "is_partition P1" "is_partition P2" shows
"is_partition (P1 \<union> P2)" using assms is_partition_def by (smt UnE UnionI disjoint_iff_not_equal)

lemma lm21: "Range Q \<union> (Range (P outside (Domain Q))) = Range (P +* Q)"
using Outside_def paste_def by (metis Range_Un_eq Un_commute equalityE)

lemma lll77c: assumes "a1 \<in> allInjections" "a2 \<in> allInjections" "Range a1 \<inter> (Range a2)={}"
"Domain a1 \<inter> (Domain a2) = {}" shows "a1 \<union> a2 \<in> allInjections" 
using assms disj_Un_runiq by (metis (no_types) Domain_converse converse_Un mem_Collect_eq)

lemma lm22: assumes "R \<in> allPartitionvalued" shows "is_partition (Range R)"
using assms 
proof -
  obtain P where
  0: "P \<in> allPartitions & R \<subseteq> UNIV \<times> P" using assms by blast
  have "Range R \<subseteq> P" using 0 by fast
  then show ?thesis using 0 assms
by (metis mem_Collect_eq subset_is_partition)
qed

lemma lm23: assumes "a1 \<in> allocationsUniverse" "a2 \<in> allocationsUniverse" "\<Union> (Range a1) \<inter> (\<Union> (Range a2))={}"
"Domain a1 \<inter> (Domain a2) = {}" shows "a1 \<union> a2 \<in> allocationsUniverse"
proof -
  let ?a="a1 \<union> a2" let ?b1="a1^-1" let ?b2="a2^-1" let ?r=Range let ?d=Domain
  let ?I=allInjections let ?P=allPartitions let ?PV=allPartitionvalued let ?u=runiq
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

lemma lm27: assumes "a \<in> allInjections" shows "a - b \<in> allInjections" using assms 
by (metis (lifting) Diff_subset converse_mono mem_Collect_eq subrel_runiq)

lemma lm30b: "{a. Domain a \<subseteq> N & Range a \<in> all_partitions G} =
(Range -` (all_partitions G)) \<inter> (Domain -`(Pow N))" 
by fastforce

lemma lm30: "possibleAllocationsRel N G = allInjections \<inter> ((Range -` (all_partitions G))
\<inter> (Domain -`(Pow N)))"
using lm19 lm30b by metis 

lemma lm28: "a \<in> possibleAllocationsRel N G = (a^-1 \<in> injections (Range a) N & Range a \<in> all_partitions G)"
using assms possible_allocations_rel_def Domain_converse Range_converse lm16
by (smt Int_Collect converse_converse injections_def lm19 mem_Collect_eq)

lemma lm28b: "a \<in> possibleAllocationsRel N G = (a \<in> injections (Domain a) (Range a) 
& Range a \<in> all_partitions G & Domain a \<subseteq> N)"
using assms lm28 possible_allocations_rel_def Domain_converse Range_converse lm16
Int_Collect converse_converse injections_def lm19 mem_Collect_eq
by (smt injectionsI order_refl)

lemma lm29: "possibleAllocationsRel N G \<supseteq> allInjections \<inter> (Range -` (all_partitions G))
\<inter> (Domain -`(Pow N))" using Domain_converse IntD2 vimage_eq lm28 
by (smt Int_Collect Pow_iff converse_converse inf_sup_aci(1) injectionsI subsetI)

corollary lm31: "possibleAllocationsRel N G = allInjections \<inter> (Range -` (all_partitions G))
\<inter> (Domain -`(Pow N))" using lm30 by (metis Int_assoc)

lemma lm32: assumes "a \<in> allPartitionvalued" shows "a - b \<in> allPartitionvalued" 
using assms subset_is_partition by fast

lemma lm35: assumes "a \<in> allocationsUniverse" shows "a - b \<in> allocationsUniverse" using assms 
lm27 lm32 by auto

lemma lm33: assumes "a \<in> allInjections" shows "a \<in> injections (Domain a) (Range a)"
using assms by (metis (lifting) injectionsI mem_Collect_eq order_refl)

lemma lm34: assumes "a \<in> allocationsUniverse" shows "a \<in> possibleAllocationsRel (Domain a) (\<Union> (Range a))"
proof -
  let ?r=Range let ?p=is_partition let ?P=all_partitions have "?p (?r a)" 
  using assms lm22 Int_iff by smt then have "?r a \<in> ?P (\<Union> (?r a))" using all_partitions_def 
  by (metis is_partition_of_def mem_Collect_eq) then show ?thesis using assms IntI 
  Int_lower1 equalityE lm19 mem_Collect_eq set_rev_mp by (metis (lifting, no_types))
qed

lemma lm36: "{X} \<in> allPartitions = (X \<noteq> {})" using is_partition_def by fastforce

lemma lm36b: "{(x, X)} - {(x, {})} \<in> allPartitionvalued" using lm36 by auto

lemma lm37: "{(x, X)} \<in> allInjections" by 
(metis Domain_converse Domain_empty Un_empty_left converse_empty empty_iff mem_Collect_eq runiq_conv_extend_singleton runiq_emptyrel runiq_singleton_rel)

lemma lm38: "{(x,X)} - {(x,{})} \<in> allocationsUniverse" using lm36b lm37 by (metis (no_types) Int_iff lm27)

lemma lm41: assumes "is_partition PP" "is_partition (Union PP)" shows "is_partition (Union ` PP)"
proof -
let ?p=is_partition let ?U=Union let ?P2="?U PP" let ?P1="?U ` PP" have 
0: "\<forall> X\<in>?P1. \<forall> Y \<in> ?P1. (X \<inter> Y = {} \<longrightarrow> X \<noteq> Y)" using assms is_partition_def Int_absorb 
Int_empty_left UnionI Union_disjoint ex_in_conv imageE by (metis (hide_lams, no_types))
{
  fix X Y assume 
  2: "X \<in> ?P1 & Y\<in>?P1 & X \<noteq> Y"
  then obtain XX YY where 
  1: "X = ?U XX & Y=?U YY & XX \<in> PP & YY\<in>PP" by blast
  have "XX \<inter> YY = {}" using 2 1 is_partition_def assms by metis
  then moreover have "\<forall> x\<in>XX. \<forall> y\<in>YY. x \<inter> y = {}" using 0 1 2 assms is_partition_def 
  by (smt UnionI disjoint_iff_not_equal)
  ultimately have "X \<inter> Y={}" using assms 0 1 2 is_partition_def by auto
}
then show ?thesis using 0 is_partition_def by metis
qed

lemma lm43: assumes "a \<in> allocationsUniverse" shows 
"(a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allocationsUniverse & 
\<Union> (Range ((a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)"
proof -
  let ?d=Domain let ?r=Range let ?U=Union let ?p=is_partition let ?P=allPartitions let ?u=runiq 
  let ?Xi="X \<union> {i}" let ?b="?Xi \<times> (?r a)" let ?a1="a - ?b" let ?Yi="a``?Xi" let ?Y="?U ?Yi" 
  let ?A2="{(i, ?Y)}" let ?a3="{(i,{})}" let ?a2="?A2 - ?a3" let ?aa1="a outside ?Xi" 
  let ?c="?a1 \<union> ?a2" let ?t1="?c \<in> allocationsUniverse" have 
  7: "?U(?r(?a1\<union>?a2))=?U(?r ?a1) \<union> (?U(?r ?a2))" by (metis Range_Un_eq Union_Un_distrib) have 
  5: "?U(?r a) \<subseteq> ?U(?r ?a1) \<union> ?U(a``?Xi) & ?U(?r ?a1) \<union> ?U(?r ?a2) \<subseteq> ?U(?r a)" by blast have
  1: "?u a & ?u (a^-1) & ?p (?r a) & ?r ?a1 \<subseteq> ?r a & ?Yi \<subseteq> ?r a" 
  using assms Int_iff lm22 mem_Collect_eq by auto then have 
  2: "?p (?r ?a1) & ?p ?Yi" using subset_is_partition Diff_subset Range_mono by metis have 
  "?a1 \<in> allocationsUniverse & ?a2 \<in> allocationsUniverse" using lm38 by (smt assms(1) lm35) then have 
  "(?a1 = {} \<or> ?a2 = {})\<longrightarrow> ?t1" using Outside_def Range_empty Un_empty_left runiqs_def 
  vimage_Collect_eq by (metis (lifting, no_types) Un_absorb2 empty_subsetI) moreover have 
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
    ultimately moreover have "?p {?r ?a1, ?Yi}" using assms 0 is_partition_def 
    by (smt IntI Int_commute empty_iff insert_iff subsetI subset_empty)
    moreover have "?U {?r ?a1, ?Yi} \<subseteq> ?r a" by auto
    then moreover have "?p (?U {?r ?a1, ?Yi})" by (metis "1" Outside_def subset_is_partition)
    ultimately moreover have "?p (?U`{(?r ?a1), ?Yi})" using lm41 by fast
    moreover have "... = {?U (?r ?a1), ?Y}" by force
    ultimately moreover have "\<forall> x \<in> ?r ?a1. \<forall> y\<in>?Yi. x \<noteq> y" 
    using IntI empty_iff by smt
    ultimately moreover have "\<forall> x \<in> ?r ?a1. \<forall> y\<in>?Yi. x \<inter> y = {}" using 0 1 2 is_partition_def
    by (metis set_rev_mp)
    ultimately have "?U (?r ?a1) \<inter> ?Y = {}" using lm42 by smt then have 
    "?U (?r ?a1) \<inter> (?U (?r ?a2)) = {}" by blast
    moreover have "?d ?a1 \<inter> (?d ?a2) = {}" by blast
    moreover have "?a1 \<in> allocationsUniverse" by (smt assms(1) lm35)
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
  have "?p (?r a)" using assms by (smt Int_iff lm22)
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
  then have "trivial ?t1" by (metis runiq_imp_triv_singleton_Im)
  moreover have "trivial ?t2" by (metis trivial_singleton)
  ultimately show ?thesis using assms 0 by blast
qed

lemma lm48: "possibleAllocationsRel N G \<subseteq> allInjections" using  lm19 by fast

lemma lm49: "possibleAllocationsRel N G \<subseteq> allPartitionvalued"
using assms lm47 is_partition_of_def is_partition_def by blast

corollary lm50: "possibleAllocationsRel N G \<subseteq> allocationsUniverse" using lm48 lm49 
by (metis (lifting, mono_tags) inf.bounded_iff)

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
  then moreover have "?aa \<in> possibleAllocationsRel (?d ?aa) (?U (?r a))"
  using lm34 by (metis (lifting, mono_tags))
  moreover have "?d a - X \<union> {i} = ?d ?aa \<union> (?d a - X \<union> {i})" using Outside_def by auto
  ultimately have "?aa \<in> possibleAllocationsRel (?d a - X \<union> {i}) (?U (?r a))"
  using lm19b by (smt in_mono)
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
  have "a \<in> allInjections" using assms by fast then have 
  0: "?u a" by simp
  moreover have "?R \<subseteq> a & ?R--i \<subseteq> a" using Outside_def by blast
  ultimately have "finite (?R -- i) & ?u (?R--i) & ?u ?R" using Outside_def runiq_def 
  by (metis assms(4) finite_subset subrel_runiq)
  then moreover have "trivial ({i}\<times>(?R``{i}))" using runiq_def 
  by (metis ll40 trivial_singleton)
  moreover have "\<forall>X. (?R -- i) \<inter> ({i}\<times>X)={}" using outside_reduces_domain by force
  ultimately have 
  1: "finite (?R--i) & finite ({i}\<times>(?R``{i})) & (?R -- i) \<inter> ({i}\<times>(?R``{i}))={} & 
  finite ({i} \<times> {?U(a``(X\<union>{i}))}) & (?R -- i) \<inter> ({i} \<times> {?U(a``(X\<union>{i}))})={}" 
  using Outside_def lm54 by fast 
  have "?R = (?R -- i) \<union> ({i}\<times>?R``{i})" by (metis l39)
  then have "setsum b ?R = setsum b (?R -- i) + setsum b ({i}\<times>(?R``{i}))" 
  using 1 setsum_Un_disjoint by (metis (lifting) setsum.union_disjoint)
  moreover have "setsum b ({i}\<times>(?R``{i})) \<le> setsum b ({i}\<times>{?U(a``(X\<union>{i}))})" using lm46 
  assms(1) 0 by metis
  ultimately have "setsum b ?R \<le> setsum b (?R -- i) + setsum b ({i}\<times>{?U(a``(X\<union>{i}))})" by linarith
  moreover have "... = setsum b (?R -- i \<union> ({i} \<times> {?U(a``(X\<union>{i}))}))" 
  using 1 setsum_Un_disjoint setsum.union_disjoint by auto
  moreover have "... = setsum b ?aa" by (metis ll52)
  ultimately show ?thesis by linarith
qed

lemma lm55: assumes "finite X" "XX \<in> all_partitions X" shows "finite XX" using 
all_partitions_def is_partition_of_def 
by (metis assms(1) assms(2) finite_UnionD mem_Collect_eq)

lemma lm58: assumes "finite N" "finite G" "a \<in> possibleAllocationsRel N G"
shows "finite a" using assms lm57 rev_finite_subset by (metis lm28b lm55)

lemma lm59: assumes "finite N" "finite G" shows "finite (possibleAllocationsRel N G)"
by (metis allocs_finite assms(1) assms(2) finite_imageI)

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

corollary lm53b: assumes "condition1 (b::_ => real) i"  "a \<in> possibleAllocationsRel N G" 
"i\<in>N-{n}" "n \<in> Domain a" "finite N" "finite G"
shows
"alpha N G b n \<ge> setsum b (a -- n)" (is "?L \<ge> ?R") using assms lm53 
proof -
let ?X="{n}" have "Domain a \<inter> ?X \<noteq> {}" using assms by blast
then show "Max ((setsum b)`(possibleAllocationsRel (N-?X) G)) \<ge> setsum b (a outside ?X)" using assms lm53 by metis
qed

lemma lm60: assumes "n \<notin> Domain a" "a \<in> possibleAllocationsRel N G" "finite G" "finite N" shows 
"alpha N G b n \<ge> setsum b (a -- n)"
proof -
let ?a="a -- n" let ?d=Domain
have "?a = a" using assms Outside_def by blast
moreover have "?d ?a \<subseteq> N-{n}" using assms lm34
by (smt Diff_iff Diff_insert_absorb calculation lm28b set_rev_mp subsetI)
ultimately have "a \<in> possibleAllocationsRel (N-{n}) G" using assms 
by (metis (full_types) lm28b)
then have "setsum b a \<in> (setsum b ` (possibleAllocationsRel (N-{n}) G))"
by blast
moreover have "finite (possibleAllocationsRel (N-{n}) G)" using allocs_finite assms lm59 by (metis finite_Diff)
ultimately show ?thesis using Max.coboundedI
by (metis (hide_lams, no_types) `a -- n = a` finite_imageI)
qed

corollary lm61: (*MC: of lm60 and lm53b*) assumes
"condition1 (b::_ => real) i" 
"a \<in> possibleAllocationsRel N G"
"i\<in>N-{n}"
"finite N"
"finite G"
shows "alpha N G b n \<ge> setsum b (a -- n)" using assms lm53b lm60 by metis

corollary lm61b: assumes "condition1 (b::_ => real) i" "a \<in> winningAllocationsRel N G c" 
"i\<in>N-{n}" "finite N" "finite G" shows "alpha N G b n \<ge> setsum b (a -- n)"  
proof -
have "a \<in> possibleAllocationsRel N G" using assms(2) lm03 try0 by fast
then show ?thesis using assms lm61 by metis
qed

corollary lm61c: assumes "condition1 (b::_ => real) i" "i\<in>N-{n}" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows 
"alpha N G b n \<ge> remainingValueRel N G t b n" (is "?L \<ge> ?R") 
using assms lm03 lm61 lm07 set_rev_mp 
proof -
have "winningAllocationRel N G t b \<in> winningAllocationsRel N G b" 
using assms(5) lm07 by (metis (hide_lams, no_types))
then show ?thesis using lm61b assms by metis
qed

lemma lm62: "(a::real) \<ge> b = (a - b \<ge> 0)" by linarith

lemma lm72b: assumes "t (winningAllocationsRel N G b) \<in> winningAllocationsRel N G b" shows
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))" using assms lm72 
by blast

corollary lm61d: assumes "condition1 (b::_=>real) i" "i\<in>N-{n}" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows "paymentsRel N G t b n \<ge> 0" 
proof - have "alpha N G b n \<ge> remainingValueRel N G t b n" using assms lm61c by metis thus ?thesis using lm62 by simp qed

abbreviation "condition2 b N == EX i1 i2. (i1 \<in> N - {i2} & i2 \<in> N - {i1} & condition1 b i1 & condition1 b i2)"

corollary lm61e:
assumes 
"condition2 (b::_=>real) N" 
"finite N"
"finite G"
"isChoice (graph {winningAllocationsRel N G b} t)"
shows
"paymentsRel N G t b n \<ge> 0"
proof -
  obtain i where 
  0: "condition1 b i & i \<in> N-{n}" using assms(1) by blast
  then have "condition1 b i" by blast moreover have "i \<in> N-{n}" using 0 by fast 
  moreover have "finite N" using assms(2) by simp moreover have "finite G" using assms(3) by auto  
  moreover have "isChoice (graph {winningAllocationsRel N G b} t)" using assms(4) by fast  
  ultimately show ?thesis by (rule lm61d)
qed

abbreviation "monotonebids == condition2"

lemma lm71: fixes N b assumes
"EX i1 i2. i1 \<in> N - {i2} & i2 \<in> N - {i1} & 
(\<forall> t t'. (trivial t & trivial t' & Union t \<subseteq> Union t') \<longrightarrow>
setsum b ({i1}\<times>t) \<le> setsum b ({i1}\<times>t') & setsum b ({i2}\<times>t) \<le> setsum b ({i2}\<times>t'))"
shows "condition2 (b) N" using assms by blast

corollary lm61f: assumes "monotonebids (b::_=>real) N" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows "\<forall>n. paymentsRel N G t b n \<ge> 0"  
proof -
{fix n have "paymentsRel N G t b n \<ge> 0" using assms by (rule lm61e)} then show ?thesis by fastforce
qed

(*MISC*)

abbreviation "Outside' X f == f outside X"
abbreviation "Chi X Y == (Y \<times> {0::nat}) +* (X \<times> {1})"
notation Chi (infix "<||" 80)
abbreviation "chii X Y == toFunction (X <|| Y)"
notation chii (infix "<|" 80)
abbreviation "chi X == indicator X"

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

lemma ll77: assumes "is_partition XX" shows "equiv (Union XX) (part2rel XX)" 
using assms ll74 ll75 ll76 equiv_def by fast

corollary ll78: assumes "runiq f" shows "equiv (Domain f) (part2rel (kernel f))"
using assms ll77 ll79 is_partition_of_def by metis

lemma assumes "f \<in> allPartitionvalued" shows "{} \<notin> Range f" using assms by (metis lm22 no_empty_eq_class)

lemma mm33: assumes "finite XX" "\<forall>X \<in> XX. finite X" "is_partition XX" shows 
"card (\<Union> XX) = setsum card XX" using assms is_partition_def card_Union_disjoint by fast

corollary mm33b: assumes "XX partitions X" "finite X" "finite XX" shows 
"card (\<Union> XX) = setsum card XX" using assms mm33 by (metis is_partition_of_def lll41)

lemma mm13: "runiq (X <|| Y)" by (metis lll59 runiq_paste2 trivial_singleton)

lemma mm14c: assumes "x \<in> X" shows "1 \<in> (X <|| Y) `` {x}" using assms toFunction_def 
paste_def Outside_def runiq_def mm14b by blast

lemma mm14d: assumes "x \<in> Y-X" shows "0 \<in> (X <|| Y) `` {x}" using assms toFunction_def
paste_def Outside_def runiq_def mm14b by blast

lemma mm14e: assumes "x \<in> X \<union> Y" shows "(X <|| Y),,x = chi X x" (is "?L=?R")using assms toFunction_def 
mm13 paste_def Outside_def mm14b mm14c mm14d l31b by (metis DiffI Un_iff indicator_simps(1) indicator_simps(2))

lemma mm14f: assumes "x \<in> X \<union> Y" shows "(X <| Y) x = chi X x" (is "?L=?R") 
using assms toFunction_def mm13 paste_def Outside_def mm14b mm14c mm14d mm14e by metis

corollary mm15: assumes "Z \<subseteq> X \<union> Y" shows "setsum (X <| Y) Z = setsum (chi X) Z" 
using assms mm14f setsum_cong by (smt in_mono)

corollary mm16: "setsum (chi X) (Z - X) = 0" by simp

corollary mm17: assumes "Z \<subseteq> X \<union> Y" shows "setsum (X <| Y) (Z - X) = 0" using assms mm16 mm15 
by (smt Diff_iff in_mono setsum.cong subsetI transfer_nat_int_sum_prod2(1))

corollary mm18: assumes "finite Z" shows "setsum (X <| Y) Z = setsum (X <| Y) (Z - X) 
+(setsum (X <| Y) (Z \<inter> X))" using mm12 assms by blast

corollary mm18b: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "setsum (X <| Y) Z = setsum (X <| Y) (Z \<inter> X)" 
using assms mm12 mm17 comm_monoid_add_class.add.left_neutral by metis

corollary mm21: assumes "finite Z" shows "setsum (chi X) Z = card (X \<inter> Z)" using assms 
setsum_indicator_eq_card by (metis Int_commute)

corollary mm22: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "setsum (X <| Y) Z = card (Z \<inter> X)"
using assms mm21 by (metis mm15 setsum_indicator_eq_card)

corollary mm28: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "(setsum (X <| Y) X) - (setsum (X <| Y) Z) =
card X - card (Z \<inter> X)" using assms mm22 by (metis Int_absorb2 Un_upper1 card_infinite equalityE setsum.infinite)

corollary mm28b: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "int (setsum (X <| Y) X) - int (setsum (X <| Y) Z) =
int (card X) - int (card (Z \<inter> X))" using assms mm22 by (metis Int_absorb2 Un_upper1 card_infinite equalityE setsum.infinite)

lemma mm28c: "int (n::nat) = real n" by simp

corollary mm28d: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "real (setsum (X <| Y) X) - real (setsum (X <| Y) Z) =
real (card X) - real (card (Z \<inter> X))" using assms mm22 by (metis Int_absorb2 Un_upper1 card_infinite equalityE setsum.infinite)

corollary setsum_Union_disjoint_2: assumes "\<forall>x\<in>X. finite x" "is_partition X" shows
"setsum f (\<Union> X) = setsum (setsum f) X" using assms setsum_Union_disjoint is_partition_def by fast

corollary setsum_Union_disjoint_3: assumes "\<forall>x\<in>X. finite x" "X partitions XX" shows
"setsum f XX = setsum (setsum f) X" using assms by (metis is_partition_of_def setsum_Union_disjoint_2)

corollary setsum_associativity: assumes "finite x" "X partitions x" shows
"setsum f x = setsum (setsum f) X" using assms setsum_Union_disjoint_3 by (metis is_partition_of_def lll41)

corollary CombiAuction24a: "(allocationsUniverse\<inter>{a. Domain a\<subseteq>N & \<Union>Range a=G})\<subseteq>possibleAllocationsRel N G"
using assms lm19 by (smt Int_iff lm34 mem_Collect_eq subsetI)
corollary CombiAuction24b: "possibleAllocationsRel N G \<subseteq> allocationsUniverse\<inter>{a. Domain a\<subseteq>N & \<Union>Range a=G}"
using assms lm19 Int_iff lm34 mem_Collect_eq subsetI lm50 is_partition_of_def
by (smt Range_converse image_iff lll81 set_rev_mp)
corollary CombiAuction24: "possibleAllocationsRel N G = (allocationsUniverse\<inter>{a. Domain a\<subseteq>N & \<Union>Range a=G})" 
(is "?L = ?R") proof -
  have "?L \<subseteq> ?R" using CombiAuction24b by metis moreover have "?R \<subseteq> ?L" using CombiAuction24a by fast
  ultimately show ?thesis by force
qed
corollary CombiAuction24d: assumes
"(b \<in> possibleAllocationsRel N G)" shows "(b\<in>allocationsUniverse& Domain b \<subseteq> N & \<Union> Range b = G)" 
using assms CombiAuction24 Int_Collect Int_iff CombiAuction24a CombiAuction24b by smt

corollary CombiAuction24c: "b \<in> possibleAllocationsRel N G=(b\<in>allocationsUniverse& Domain b\<subseteq>N & \<Union>Range b = G)" 
using assms CombiAuction24 Int_Collect Int_iff CombiAuction24a CombiAuction24b CombiAuction24d by smt

corollary lm35d: assumes "a \<in> allocationsUniverse" shows "a outside X \<in> allocationsUniverse" using assms Outside_def
by (metis (lifting, mono_tags) lm35)

end
