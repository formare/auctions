theory g

imports "../CombinatorialVickreyAuction"
"~~/src/HOL/Library/Code_Target_Nat"
(* "../CombinatorialVickreyAuctionSoundness" *)
"../CombinatorialAuctionProperties"
Relation

begin

lemma lm63: assumes "Y \<in> set (all_partitions_alg X)" shows "distinct Y"
using assms coarser_partitions_with_list_distinct distinct_sorted_list_of_set 
by (metis all_partitions_alg_def all_partitions_paper_equiv_alg')

lemma lm64: assumes "finite X" shows "set (sorted_list_of_set X)=X" using assms 
by simp

lemma lm65: assumes "finite G" shows 
"all_partitions G = set ` (set (all_partitions_alg G))"
using lm64 all_partitions_alg_def all_partitions_def all_partitions_paper_equiv_alg
lm63 
by (metis assms distinct_sorted_list_of_set image_set order_refl)

term "all_partitions G"

lemma assumes "Y \<in> set (all_partitions_alg G)" "card N > 0" "finite N" "finite G" 
shows "injections (set Y) N = set (injections_alg Y N)"
using assms injections_equiv lm63 all_partitions_paper_equiv_alg lm64 lm65 
by metis

lemma lm66: assumes "\<forall>l \<in> set (g1 G). set (g2 l N) = f2 (set l) N" shows 
"set [set (g2 l N). l <- g1 G] = {f2 P N| P. P \<in> set (map set (g1 G))}" using assms by auto
lemma lm66b: fixes G N f1 f2 g1 g2 shows "(\<forall>l \<in> set (g1 G). set (g2 l N) = f2 (set l) N) --> 
{f2 P N| P. P \<in> set (map set (g1 G))} = set [set (g2 l N). l <- g1 G]" using lm66 
proof -
  {
    assume "(\<forall>l \<in> set (g1 G). set (g2 l N) = f2 (set l) N)"
    then have "{f2 P N| P. P \<in> set (map set (g1 G))} = set [set (g2 l N). l <- g1 G]" by auto
  }
  thus ?thesis by fast
qed
lemma lm67: assumes "l \<in> set (all_partitions_list G)" "distinct G" shows "distinct l" 
using assms coarser_partitions_with_list_distinct all_partitions_list_def
by (metis all_partitions_paper_equiv_alg')
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

lemma assumes "card N > 0" "distinct G" shows 
"possibleAllocationsRel N (set G) = possibleAllocationsAlg2 N G" (is "?L = ?R") using assms lm70 
possible_allocations_rel_def 
proof -
  let ?LL="\<Union> {injections P N| P. P \<in> all_partitions (set G)}"
  let ?RR="\<Union> (set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G])"
  have "?LL = ?RR" using assms apply (rule lm70) done
  then have "converse ` ?LL = converse ` ?RR" by presburger
  thus ?thesis using possible_allocations_rel_def by force
qed

lemma lm54:  assumes "trivial X" shows "finite X" 
using trivial_def by (metis assms finite.simps trivial_cases)

abbreviation "isChoice R == \<forall>x. R``{x} \<subseteq> x"
abbreviation "dualOutside R Y == R - (Domain R \<times> Y)"
notation dualOutside (infix "|-" 75)
notation Outside (infix "-|" 75)

abbreviation "allPartitions == {X. is_partition X}"
lemma "allPartitions \<subseteq> Pow UNIV" by simp       
abbreviation "allPartitionvalued == \<Union> P \<in> allPartitions. Pow (UNIV \<times> P)"
lemma "allPartitionvalued \<subseteq> Pow (UNIV \<times> (Pow UNIV))" by simp
abbreviation "allInjections == {R. (runiq R) & (runiq (R^-1))}"
abbreviation "allAllocations == allInjections \<inter> allPartitionvalued"
abbreviation "totalRels X Y == {R. Domain R = X & Range R \<subseteq> Y}"
abbreviation "strictCovers G == Union -` {G}"

lemma "R |- Y = (R^-1 -| Y)^-1" using Outside_def by auto
lemma lm24: "injections' X Y = injections X Y" using injections_def by metis
lemma lm25: "injections' X Y \<subseteq> allInjections" by fast
lemma lm25b: "injections X Y \<subseteq> allInjections" using assms possible_allocations_rel_def 
injections_def all_partitions_def is_partition_of_def by blast
lemma lm26: "injections' X Y = totalRels X Y \<inter> allInjections" by fastforce

lemma lm47: fixes N::"participant set" fixes G::goods fixes a::"allocation" assumes 
"a \<in> possibleAllocationsRel N G" shows 
"a^-1 \<in> injections (Range a) N & Range a partitions G & Domain a \<subseteq> N"
using assms all_partitions_def Domain_converse allocation_injective converse_converse 
image_iff injections_def mem_Collect_eq by smt

lemma lll23: assumes "finite A" shows "setsum f A = setsum f (A \<inter> B) + setsum f (A - B)" using 
assms by (metis DiffD2 Int_iff Un_Diff_Int Un_commute finite_Un setsum.union_inter_neutral)

lemma shows "(P||(Domain Q)) +* Q = Q" by (metis Int_lower2 ll41 ll56)

lemma lll77: assumes "Range P \<inter> (Range Q)={}" "runiq (P^-1)" "runiq (Q^-1)" shows "runiq ((P \<union> Q)^-1)"
using assms
by (metis Domain_converse converse_Un disj_Un_runiq)

lemma lll77b: assumes "Range P \<inter> (Range Q)={}" "runiq (P^-1)" "runiq (Q^-1)" 
shows "runiq ((P +* Q)^-1)"
using lll77 assms subrel_runiq by (metis converse_converse converse_subset_swap paste_sub_Un)

lemma assumes "runiq P" shows "P\<inverse>``((Range P)-X) \<inter> ((P\<inverse>)``X) = {}"
using assms ll71 by blast

lemma lll78: assumes "runiq (P\<inverse>)" shows "P``(Domain P - X) \<inter> (P``X) = {}"
using assms ll71 by fast

lemma lll84: "P``(X \<inter> Domain P)=P``X" by blast

lemma lll85b: "Range (R outside X) = R``(Domain R - X)" 
using assms by (metis Diff_idemp ImageE Range.intros Range_outside_sub_Image_Domain lll01 lll99 order_class.order.antisym subsetI)

lemma lll85: "Range (P||X) = P``X" using assms lll85b lll01
proof -
  let ?p="P||X" let ?d=Domain let ?r=Range
  have "?r ?p=?p``(?d ?p)" by auto moreover have 
  "... = ?p``(X \<inter> ?d ?p)" using restrict_def by blast moreover have 
  "... \<subseteq> P``(X \<inter> ?d ?p)" using restrict_def by auto
  moreover have "... = P``X" by (metis Image_within_domain inf_commute inf_left_idem ll41)
  moreover have "P``X \<subseteq> ?r ?p" using restrict_def by fast
  ultimately show ?thesis by simp
qed

lemma lll82: assumes 
"runiq (f::(('a \<times> ('b set)) set))"
"(x::'a) \<in> Domain f" shows "f,,x = f,,,x"
(* CL: Interesting: metis says that eval_rel_def is unused in the proof, but when I use it,
   the proof takes much longer (too long for me to wait) *)
using assms by (metis Image_runiq_eq_eval cSup_singleton)

lemma lll79: assumes "\<Union> XX \<subseteq> X" "x \<in> XX" "x \<noteq> {}" shows "x \<inter> X \<noteq> {}" using assms by blast

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

lemma lll86: assumes "X \<inter> Y={}" shows "R``X = (R outside Y)``X"
using assms Outside_def Image_def by blast

lemma lm02: "arg_max' f A = { x \<in> A . f x = Max (f ` A) }" using assms
by simp

lemma lm04: "graph (X \<inter> Y) f \<subseteq> graph X f || Y" using graph_def assms restrict_def
by (smt Int_iff mem_Collect_eq restrict_ext subrelI)

lemma lm06: "graph X f = Graph f || X" using graph_def Graph_def restrict_def
by (smt inf_top.left_neutral  lm04 mem_Collect_eq prod.inject restrict_ext subsetI subset_antisym)

lemma lm05: "graph (X \<inter> Y) f = graph X f || Y" using lll02 lm06 by metis

lemma lm07: assumes "isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))" shows 
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

corollary lm03: "winningAllocationsRel N G (b::altbids) \<subseteq> possibleAllocationsRel N G" 
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

lemma lm16: "converse `allInjections = allInjections" by auto

lemma lm17: "possible_allocations_rel G N = allInjections \<inter> {a. Domain a \<in> all_partitions G & Range a \<subseteq> N}"
using lm14 lm15 by blast

lemma lm18: "converse`(A \<inter> B)=converse`A \<inter> (converse`B)" by force

lemma lm19: "possibleAllocationsRel N G = allInjections \<inter> {a. Domain a \<subseteq> N & Range a \<in> all_partitions G}"
using assms lm13 lm16 lm17 lm18 
proof -
  let ?A="possible_allocations_rel G N" let ?c=converse let ?I=allInjections 
  let ?P="all_partitions G" let ?d=Domain let ?r=Range
  have "?c`?A = (?c`?I) \<inter> ?c` ({a. ?r a \<subseteq> N & ?d a \<in> ?P})" using lm18 lm17 by force
  moreover have "... = (?c`?I) \<inter> {aa. ?d aa \<subseteq> N & ?r aa \<in> ?P}" using lm16 by fastforce
  moreover have "... = ?I \<inter> {aa. ?d aa \<subseteq> N & ?r aa \<in> ?P}" using lm16 by metis
  ultimately show ?thesis by presburger
qed

corollary lm19b: "possibleAllocationsRel N1 G \<subseteq> possibleAllocationsRel (N1 \<union> N2) G"
using lm19 assms by auto

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

lemma lm23: assumes "a1 \<in> allAllocations" "a2 \<in> allAllocations" "\<Union> (Range a1) \<inter> (\<Union> (Range a2))={}"
"Domain a1 \<inter> (Domain a2) = {}" shows "a1 \<union> a2 \<in> allAllocations"
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

lemma lm30: "possibleAllocationsRel N G \<subseteq> allInjections \<inter> (Range -` (all_partitions G))
\<inter> (Domain -`(Pow N))"
using assms possible_allocations_rel_def lm25b lm25 lm26 Domain_converse
Range_converse Pow_def IntD2 image_subsetI lm17 mem_Collect_eq vimage_eq
by force

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
\<inter> (Domain -`(Pow N))" using lm29 lm30 by (smt subset_antisym)

lemma lm32: assumes "a \<in> allPartitionvalued" shows "a - b \<in> allPartitionvalued" 
using assms subset_is_partition by fast

lemma lm35: assumes "a \<in> allAllocations" shows "a - b \<in> allAllocations" using assms 
lm27 lm32 by auto

lemma lm33: assumes "a \<in> allInjections" shows "a \<in> injections (Domain a) (Range a)"
using assms by (metis (lifting) injectionsI mem_Collect_eq order_refl)

lemma lm34: assumes "a \<in> allAllocations" shows "a \<in> possibleAllocationsRel (Domain a) (\<Union> (Range a))"
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

lemma lm38: "{(x,X)} - {(x,{})} \<in> allAllocations" using lm36b lm37 by (metis (no_types) Int_iff lm27)

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

lemma lm40: assumes "runiq (R^-1)" "runiq R" "X1 \<inter> X2 = {}" shows "R``X1 \<inter> (R``X2) = {}"
using assms runiq_def
by (metis disj_Domain_imp_disj_Image empty_subsetI inf_assoc inf_bot_right)

lemma lm42: "(\<forall> x \<in> X. \<forall> y \<in> Y. x \<inter> y = {})=(\<Union> X \<inter> (\<Union> Y)={})" by blast

lemma "Domain ((a outside (X \<union> {i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) ) 
\<subseteq> Domain a - X \<union> {i}" using assms Outside_def by auto

lemma lm43: assumes "a \<in> allAllocations" shows 
"(a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allAllocations & 
\<Union> (Range ((a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)"
proof -
  let ?d=Domain let ?r=Range let ?U=Union let ?p=is_partition let ?P=allPartitions let ?u=runiq 
  let ?Xi="X \<union> {i}" let ?b="?Xi \<times> (?r a)" let ?a1="a - ?b" let ?Yi="a``?Xi" let ?Y="?U ?Yi" 
  let ?A2="{(i, ?Y)}" let ?a3="{(i,{})}" let ?a2="?A2 - ?a3" let ?aa1="a outside ?Xi" 
  let ?c="?a1 \<union> ?a2" let ?t1="?c \<in> allAllocations" have 
  7: "?U(?r(?a1\<union>?a2))=?U(?r ?a1) \<union> (?U(?r ?a2))" by (metis Range_Un_eq Union_Un_distrib) have 
  5: "?U(?r a) \<subseteq> ?U(?r ?a1) \<union> ?U(a``?Xi) & ?U(?r ?a1) \<union> ?U(?r ?a2) \<subseteq> ?U(?r a)" by blast have
  1: "?u a & ?u (a^-1) & ?p (?r a) & ?r ?a1 \<subseteq> ?r a & ?Yi \<subseteq> ?r a" 
  using assms Int_iff lm22 mem_Collect_eq by auto then have 
  2: "?p (?r ?a1) & ?p ?Yi" using subset_is_partition Diff_subset Range_mono by metis have 
  "?a1 \<in> allAllocations & ?a2 \<in> allAllocations" using lm38 by (smt assms(1) lm35) then have 
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
    moreover have "?a1 \<in> allAllocations" by (smt assms(1) lm35)
    moreover have "?a2 \<in> allAllocations" using lm38 by fastforce
    ultimately have ?t1 using lm23 by smt (*MC: use solve_direct *)
    then have ?thesis using 6 7 by presburger
  }
  then show ?thesis using 3 by linarith
qed

lemma "(R - ((X\<union>{i})\<times>(Range R))) = (R outside X) outside {i}" using Outside_def 
by (metis ll52)

lemma "{(i, x)} - {(i,y)} = {i} \<times> ({x}-{y})" by fast

lemma lm44: "{x}-{y}={} = (x=y)" by auto

lemma assumes "R \<noteq> {}" "Domain R \<inter> X \<noteq> {}" shows "R``X \<noteq> {}" using assms
by (metis Image_outside_domain Int_commute)

lemma "R``{}={}" 
by (metis Image_empty)

lemma lm45: assumes "Domain a \<inter> X \<noteq> {}" "a \<in> allAllocations" shows
"\<Union>(a``X) \<noteq> {}" (*MC: Should be stated in more general form *)
proof -
  let ?p=is_partition let ?r=Range
  have "?p (?r a)" using assms by (smt Int_iff lm22)
  moreover have "a``X \<subseteq> ?r a" by fast
  ultimately have "?p (a``X)" using assms subset_is_partition by blast
  moreover have "a``X \<noteq> {}" using assms by fast
  ultimately show ?thesis by (metis Union_member all_not_in_conv no_empty_eq_class)
qed

corollary lm45b: assumes "Domain a \<inter> X \<noteq> {}" "a \<in> allAllocations" shows 
"{\<Union>(a``(X\<union>{i}))}-{{}} = {\<Union>(a``(X\<union>{i}))}" using assms lm45 by fast

corollary lm43b: assumes "a \<in> allAllocations" shows 
"(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> allAllocations & 
\<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})))) = \<Union>(Range a)"
proof -
have "a - ((X\<union>{i})\<times>(Range a)) = a outside (X \<union> {i})" using Outside_def by metis
moreover have "(a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allAllocations"
using assms lm43 by fastforce
moreover have "\<Union> (Range ((a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)"
using assms lm43 by (metis (no_types))
ultimately have
"(a outside (X\<union>{i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allAllocations & 
\<Union> (Range ((a outside (X\<union>{i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)" by
presburger
moreover have "{(i, \<Union> (a``(X \<union> {i})))} - {(i,{})} = {i} \<times> ({\<Union> (a``(X\<union>{i}))} - {{}})" 
by fast
ultimately show ?thesis by auto
qed

corollary lm43c: assumes "a \<in> allAllocations" "Domain a \<inter> X \<noteq> {}" shows 
"(a outside (X\<union>{i})) \<union> ({i}\<times>{\<Union>(a``(X\<union>{i}))}) \<in> allAllocations & 
\<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>{\<Union>(a``(X\<union>{i}))}))) = \<Union>(Range a)"
using assms lm43b lm45b
proof -
let ?t1="(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> allAllocations"
let ?t2="\<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})))) = \<Union>(Range a)"
have 
0: "a \<in> allAllocations" using assms(1) by fast 
then have "?t1 & ?t2" using lm43b 
proof - 
(*MC: Isabelle cannot do elementary logic steps, only could make it work via this ugly proof found by sledgehammer *)
  have "a \<in> allAllocations \<longrightarrow> a -| (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allAllocations"
    using lm43b by fastforce
  hence "a -| (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allAllocations"
    by (metis "0")
  thus "a -| (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allAllocations \<and> \<Union>Range (a -| (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}})) = \<Union>Range a"
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
  0: "?U ?t1 \<subseteq> ?U ?t2" by blast
  have "?u a" using assms by fast 
  moreover have "?R \<subseteq> a" using Outside_def by blast ultimately
  have "?u ?R" using Outside_def subrel_runiq by metis
  then have "trivial ?t1" by (metis runiq_imp_triv_singleton_Im)
  moreover have "trivial ?t2" by (metis trivial_singleton)
  ultimately show ?thesis using assms 0 by blast
qed

lemma lm48: "possibleAllocationsRel N G \<subseteq> allInjections" using assms
by (metis (lifting, no_types) inf.cobounded1 inf_sup_aci(2) lm31)

lemma lm49: "possibleAllocationsRel N G \<subseteq> allPartitionvalued"
using assms lm47 is_partition_of_def is_partition_def by blast

corollary lm50: "possibleAllocationsRel N G \<subseteq> allAllocations" using lm48 lm49 by simp

lemma lm51: assumes  
"a \<in> possibleAllocationsRel N G" 
"i\<in>N-X" 
"Domain a \<inter> X \<noteq> {}" 
shows 
"a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))}) \<in> possibleAllocationsRel (N-X) (\<Union> (Range a))"
proof -
  let ?R="a outside X" let ?I="{i}" let ?U=Union let ?u=runiq let ?r=Range let ?d=Domain
  let ?aa="a outside (X \<union> {i}) \<union> ({i} \<times> {?U(a``(X\<union>{i}))})" have 
  1: "a \<in> allAllocations" using assms lm50 by (metis (lifting, no_types) set_rev_mp)
  have "i \<notin> X" using assms by fast then have 
  2: "?d a - X \<union> {i} = ?d a \<union> {i} - X" by fast
  have "a \<in> allAllocations" using 1 by fast moreover have "?d a \<inter> X \<noteq> {}" using assms by fast 
  ultimately have "?aa \<in> allAllocations & ?U (?r ?aa) = ?U (?r a)" apply (rule lm43c) done
  then moreover have "?aa \<in> possibleAllocationsRel (?d ?aa) (?U (?r a))"
  using lm34 by (metis (lifting, no_types))
  moreover have "?d a - X \<union> {i} = ?d ?aa \<union> (?d a - X \<union> {i})" using Outside_def by auto
  ultimately have "?aa \<in> possibleAllocationsRel (?d a - X \<union> {i}) (?U (?r a))"
  using lm19b by (smt in_mono)
  then have "?aa \<in> possibleAllocationsRel (?d a \<union> {i} - X) (?U (?r a))" using 2 by simp
  moreover have "?d a \<subseteq> N" using assms lm19 
  by auto 
  then moreover have "(?d a \<union> {i} - X) \<union> (N - X) = N - X" using assms by fast
  ultimately have "?aa \<in> possibleAllocationsRel (N - X) (?U (?r a))" using lm19b 
  by (metis (lifting, no_types) in_mono)
  then show ?thesis by fast
qed

lemma lm52: assumes 
"condition1 (b::altbids) (i::participant)" 
"(a::allocation) \<in> allAllocations" 
"Domain a \<inter> (X::participant set) \<noteq> {}" 
"finite a" shows 
"proceeds b (a outside X) \<le> proceeds b (a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))}))"
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

lemma lm56: "R \<subseteq> (Domain R) \<times> (Range R)" by auto

lemma lm57: "(finite (Domain Q) & finite (Range Q)) = finite Q" using 
rev_finite_subset finite_SigmaI lm56 finite_Domain finite_Range by metis

lemma lm58: assumes "finite N" "finite G" "a \<in> possibleAllocationsRel N G"
shows "finite a" using assms lm57 mem_Collect_eq rev_finite_subset 
by (metis lm28b lm55)

lemma lm59: assumes "finite N" "finite G" shows "finite (possibleAllocationsRel N G)"
by (metis allocs_finite assms(1) assms(2) finite_imageI)

corollary lm53: assumes
"condition1 (b::altbids) (i::participant)" 
"(a::allocation) \<in> possibleAllocationsRel N G" 
"i\<in>N-X" 
"Domain a \<inter> (X::participant set) \<noteq> {}"
"finite N"
"finite G"
shows
"Max ((proceeds b)`(possibleAllocationsRel (N-X) G)) \<ge> 
proceeds b (a outside X)"
proof -
let ?aa="(a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))}))"
have "a \<in> allAllocations" using assms(2) lm50 by blast 
moreover have "finite a" using assms lm58 by presburger ultimately have 
0: "proceeds b (a outside X) \<le> proceeds b ?aa" using assms lm52 by presburger
have "?aa \<in> possibleAllocationsRel (N-X) (\<Union> (Range a))" using assms lm51 by presburger
moreover have "\<Union> (Range a) = G" using assms lm47 is_partition_of_def by metis
ultimately have "proceeds b ?aa \<in> (proceeds b)`(possibleAllocationsRel (N-X) G)" 
by (metis imageI)
moreover have "finite ((proceeds b)`(possibleAllocationsRel (N-X) G))" using assms lm59 by auto
ultimately have "proceeds b ?aa \<le> Max ((proceeds b)`(possibleAllocationsRel (N-X) G))" by auto
then show ?thesis using 0 by linarith
qed

corollary lm53b: assumes
"condition1 (b::altbids) (i::participant)" 
"(a::allocation) \<in> possibleAllocationsRel N G" 
"i\<in>N-{n}" 
"n \<in> Domain a"
"finite N"
"finite G"
shows
"alpha N G b n \<ge> proceeds b (a -- n)" using assms lm53 by simp

lemma lm60: assumes "n \<notin> Domain a" "a \<in> possibleAllocationsRel N G" "finite G" "finite N" shows 
"alpha N G b n \<ge> proceeds b (a -- n)"
proof -
let ?a="a -- n" let ?d=Domain
have "?a = a" using assms Outside_def by blast
moreover have "?d ?a \<subseteq> N-{n}" using assms lm34
by (smt Diff_iff Diff_insert_absorb calculation lm28b set_rev_mp subsetI)
ultimately have "a \<in> possibleAllocationsRel (N-{n}) G" using assms 
by (metis (full_types) lm28b)
then have "proceeds b a \<in> (proceeds b ` (possibleAllocationsRel (N-{n}) G))"
by blast
moreover have "finite (possibleAllocationsRel (N-{n}) G)" using allocs_finite assms by simp
ultimately show ?thesis using Max.coboundedI
by (metis (hide_lams, no_types) `a -- n = a` finite_imageI)
qed

corollary lm61: (*MC: of lm60 and lm53b*) assumes
"condition1 b i" 
"a \<in> possibleAllocationsRel N G" 
"i\<in>N-{n}" 
"finite N"
"finite G"
shows "alpha N G b n \<ge> proceeds b (a -- n)" using assms lm53b lm60 by metis

corollary lm61b: assumes
"condition1 b i" 
"a \<in> winningAllocationsRel N G c" 
"i\<in>N-{n}" 
"finite N"
"finite G"
shows "alpha N G b n \<ge> proceeds b (a -- n)" using assms lm03 lm61 by blast

corollary lm61c: assumes
"condition1 b i" 
"i\<in>N-{n}" 
"finite N"
"finite G"
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))"
shows "alpha N G b n \<ge> remainingValueRel N G t b n" using assms lm03 lm61 lm07 by simp

term "alpha N G b n"

lemma lm62: "(a::real) \<ge> b = (a - b \<ge> 0)" by linarith

corollary lm61d: assumes
"condition1 b i" 
"i\<in>N-{n}" 
"finite N"
"finite G"
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))"
shows "paymentsRel N G t b n \<ge> 0" using assms lm61c lm62 by auto

abbreviation "condition2 b N == EX i1 i2. (i1 \<in> N - {i2} & i2 \<in> N - {i1} & condition1 b i1 & condition1 b i2)"

corollary lm61e:
assumes 
"condition2 (b::altbids) N" 
"finite (N::participant set)"
"finite (G::goods)"
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))"
shows
"paymentsRel N G t b n \<ge> 0"
proof -
  obtain i where 
  0: "i \<in> N-{n} & condition1 b i" using assms(1) by blast
  show ?thesis using 0 assms lm61d by auto
qed

abbreviation "monotonebids == condition2"

corollary lm61f:
assumes 
"monotonebids (b::altbids) N" 
"finite (N::participant set)"
"finite (G::goods)"
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))"
shows
"\<forall>n::participant. paymentsRel N G t b n \<ge> 0" using assms lm61e by presburger

(* BIGSKIP
lemma "possibleAllocationsRel N G \<subseteq> allAllocations" using assms possible_allocations_rel_def 
injections_def all_partitions_def is_partition_of_def lm24 lm25 lm25b lm26 
sorry

lemma assumes "X \<in> (strictCovers G)" shows "(\<Union> X) = G" sorry
lemma "all_partitions G = allPartitions \<inter> (strictCovers G)" sorry
lemma "possibleAllocationsRel N G \<subseteq> allAllocations \<inter> ((Union \<circ> Range) -` {G}) \<inter> (Dom -` (Pow N))" 
using assms possible_allocations_rel_def sorry

lemma assumes "a1 \<in> possibleAllocationsRel N1 G1" "a2 \<in> possibleAllocationsRel N2 (G2-G1)"
shows "(a1 +* a2) \<in> possibleAllocationsRel (N1 \<union> N2) (G1 \<union> G2)" using assms 
possible_allocations_rel_def
proof -
let ?a="a1 +* a2" let ?u=runiq let ?d=Domain let ?r=Range let ?I=allInjections 
let ?N="N1 \<union> N2" let ?G="G1 \<union> G2" let ?P=all_partitions' let ?g2="G2-G1" have 
0: "?d a1 \<subseteq> N1 & ?d a2 \<subseteq> N2 & ?r a1 \<in> ?P G1 & ?r a2 \<in> ?P ?g2" using assms lm19 sorry
have "?u a1 & ?u (a1^-1)" using assms(1) possible_allocations_rel_def sorry
moreover
have "?u a2 & ?u (a2^-1)" using assms(1) possible_allocations_rel_def sorry
ultimately moreover have "?u ?a" by (metis runiq_paste2)
moreover have "?r a1 \<inter> (?r a2)={}" sorry
then moreover have "?u (?a^-1)" using runiq_converse_paste assms by (metis calculation(1) calculation(2) lll77b)
ultimately moreover have "?a \<in> ?I" by fast
moreover have "?d ?a \<subseteq> ?N" using assms paste_def 0 by (metis Un_mono paste_Domain)
moreover have "?r ?a \<subseteq> (?r a1) \<union> (?r a2)" by (metis paste_Range)
moreover have "is_partition (?r a1) & is_partition (?r a2)" sorry
then moreover have "is_partition ((?r a1) \<union> (?r a2))" using assms lm20 0 by (metis (lifting, mono_tags) Diff_disjoint mem_Collect_eq)
moreover have "is_partition (?r ?a)" using 0 assms is_partition_of_def
by (metis calculation(10) calculation(8) subset_is_partition)
moreover have "?r a1 \<inter> (?r a2)={}" by (metis calculation(4))
ultimately moreover have "?r ?a = (?r a1) \<union> (?r a2)" using paste_def lm21 assms 0 sorry
show ?thesis sorry
qed

lemma assumes "n \<notin> N" shows "Max ((proceeds b)`(possibleAllocationsRel (N-{n}) G)) = 
proceeds b (winningAllocationRel N G t b -- n)" using assms sorry

lemma lll74: assumes "a\<inverse> \<in> possible_allocations_rel G N" 
"Y2 \<inter> (G - a,,,x)={}"
"Y2 \<noteq> {}"
shows "(a +< (x,Y2))\<inverse> \<in> possible_allocations_rel (G-(a,,,x)\<union>Y2) (N \<union> {x})"
proof -
let ?Y1="a,,,x" let ?u=runiq let ?A=possible_allocations_rel let ?aa="a\<inverse>" let ?I=injections
let ?P=all_partitions let ?r=Range let ?a2="a +< (x, Y2)" let ?d=Domain
obtain pG where 
1: "?aa \<in> ?I pG N & pG \<in> ?P G" using assms(1) possible_allocations_rel_def by fastforce
have "?u a" using 1 injections_def
by (smt converse_converse mem_Collect_eq)
then have 
12: "?u (a +< (x,Y2))" using lll73 by metis
have "?r (a -- x)=a``(?d a - {x})" using Outside_def by blast
moreover have 
0: "?u ?aa & ?u a" using assms by (metis `runiq a` lll81) ultimately
have "?r (a -- x) \<inter> (a``{x}) = {}" using lll78 
by metis 
moreover have 
3: "(a -- x) \<union> {(x, Y2)} = ?a2" using paste_def 
by (metis Domain_empty Domain_insert fst_conv snd_conv)
have 
6: "?r ?a2 = ?r (a -- x) \<union> {Y2}" using 3 by auto
moreover have "?r a = ?r (a -- x) \<union> (a``{x})" using Outside_def
by blast
ultimately moreover have "?r (a -- x) = ?r a - a``{x}" by auto
moreover have "is_partition (?r a) & (\<Union> (?r a))=G" using 1 by (metis Domain_converse assms(1) is_partition_of_def lll81)
ultimately moreover have "a``{x} \<subseteq> ?r a" by (metis Un_upper2)
ultimately have 
5: "(?r (a -- x)) partitions (G - \<Union>(a``{x}))" using lll80 by metis
then have 
4: "\<Union> (?r (a -- x)) = (G - a,,,x)" unfolding is_partition_of_def by fast
then have "Y2 \<notin> (?r (a -- x))" using lll79 assms subsetI by metis
then have "?r {(x, Y2)} \<inter> ?r (a -- x) = {}" using assms by blast
moreover have "?u {(x, Y2)}" by (metis runiq_singleton_rel)
moreover have "(a--x)\<inverse> \<subseteq> ?aa" using Outside_def
by blast
moreover then  have "?u ((a -- x)\<inverse>)" using 0 subrel_runiq by metis
ultimately moreover have "?u (((a -- x) \<union> {(x, Y2)})\<inverse>)" using 0 by (metis 
IntI Range_insert empty_iff insert_iff runiq_conv_extend_singleton)
ultimately have 
11: "?u (?a2\<inverse>)" using 3 by metis
moreover have "?d a \<subseteq> N" using assms lll81 by simp
moreover have "?d {(x, Y2)}={x}" by simp
ultimately moreover have "?r (?a2\<inverse>) \<subseteq> N \<union> {x}" using paste_Domain
by (smt Domain_insert Range_converse Un_iff fst_conv set_rev_mp subsetI)
ultimately have 
13: "?a2\<inverse> \<in> injections (?r ?a2) (N \<union> {x})" using 12
 Domain_converse converse_converse injectionsI by (metis (hide_lams, no_types))
have "Y2 \<inter> \<Union> (?r (a -- x)) = {}" using 4 assms by presburger
moreover have "is_partition (?r (a --x ))" using 5 by (metis is_partition_of_def)
ultimately have "is_partition (insert Y2 (?r (a -- x)))" using partition_extension1 assms
by blast
then have "is_partition (?r (a -- x) \<union> {Y2})" by auto
then have "is_partition (?r ?a2)" by (metis "6")
moreover have "\<Union> (?r ?a2) = \<Union> (?r (a -- x)) \<union> Y2"
by (metis "6" Union_Un_distrib cSup_singleton)
moreover have "... = (G - (a,,,x)) \<union> Y2" by (metis "4")
ultimately have "(?r ?a2) partitions ((G - (a,,,x)) \<union> Y2)"
by (metis "6" Un_commute insert_def is_partition_of_def singleton_conv)
then have "?r ?a2 \<in> ?P (G - (a,,,x) \<union> Y2)" using all_partitions_def by (metis mem_Collect_eq)
then have "(?a2\<inverse>) \<in> injections (?r ?a2) (N \<union> {x}) & ?r ?a2 \<in> ?P (G - (a,,,x) \<union> Y2)"
using 13 by fast
then show ?thesis using possible_allocations_rel_def by auto
qed

lemma lll75: assumes "finite a" "(b::altbids) (xx, yy1) \<le> b (xx, yy2)" shows 
"setsum b ((a::allocation) +< (xx,yy1)) \<le> setsum b (a +< (xx,yy2))"
proof -
  let ?z1="(xx, yy1)" let ?z2="(xx, yy2)" let ?a0="a -- xx" let ?a1="a +< ?z1" let ?a2="a +< ?z2"
  have 
  0: "{?z1} || {xx}={?z1} & {?z2}||{xx}={?z2}" using restrict_def by auto

  have "finite {?z1} & finite {?z2}" by simp then have 
  2: "finite ?a1 & finite ?a2" using paste_def assms 
  by (metis finite_Un finite_insert outside_union_restrict)

  have "?a1 = (?a1 -- xx) \<union> (?a1 || {xx}) " 
  using paste_def Outside_def outside_union_restrict by metis
  have "setsum b ?a1 = setsum b (?a1||{xx}) + setsum b (?a1 outside {xx})" using 2
  by (metis finite_Un lll00 lll01 lll06b outside_union_restrict setsum.union_disjoint)
  moreover have 
  1: "?a1 = a +* {?z1} & ?a2 = a +* {?z2}" by (metis fst_conv snd_conv)
  then have "?a1||{xx} = (a || {xx}) +* ({?z1} || {xx})" using lll71 by fastforce

  moreover have "... = {?z1}||{xx}" using ll41 ll56 by (metis "0" Domain_empty Domain_insert Int_lower2)
  ultimately have 
  "setsum b ?a1 = setsum b ({?z1}) + setsum b (?a1 outside {xx})" 
  by (metis "0") then have
  11: "setsum b ?a1 = b ?z1 + setsum b (?a1 outside {xx})"
  by simp

  have "setsum b ?a2 = setsum b (?a2||{xx}) + setsum b (?a2 outside {xx})" using 2
  by (metis finite_Un lll00 lll01 lll06b outside_union_restrict setsum.union_disjoint)
  have "?a2||{xx} = (a || {xx}) +* ({?z2} || {xx})" using lll71 by fastforce
  moreover have "... = {?z2}||{xx}" using ll41 ll56 by (metis "0" Domain_empty Domain_insert Int_lower2)
  ultimately have "setsum b ?a2 = setsum b ({?z2}) + setsum b (?a2 outside {xx})" using 1 0  by (metis 
  `proceeds b (a +< (xx, yy2)) = proceeds b ((a +< (xx, yy2)) || {xx}) + proceeds b ((a +< (xx, yy2)) -- xx)`) 
  then have
  12: "setsum b ?a2 = b ?z2 + setsum b (?a2 outside {xx})" by simp

  have "?a1 outside {xx} = (a outside {xx}) +* ({?z1} outside {xx})" 
  using lll72 by (metis "1")
  moreover have "... = (a outside {xx}) +* {}" using 1
  by (metis "0" Diff_insert_absorb empty_iff lll04 restrict_empty)
  ultimately have "?a1 outside {xx} = a outside {xx}"
  by (metis Un_empty_right outside_union_restrict paste_outside_restrict restrict_empty)
  moreover have "... = ?a2 outside {xx}" using lll72 0 1 lll04 
  Un_empty_right outside_union_restrict paste_outside_restrict restrict_empty 
  by (metis Diff_cancel) (*MC: Diff_insert_absorb AND empty_iff not needed now??! *)
  ultimately show ?thesis using 11 12 assms by smt
qed
BIGSKIP*)
(*BIGSKIP
lemma lll76: assumes "a \<in> possible_allocations_rel G N"
"n \<in> Range a"
"finite (possibleAllocationsRel (N-{n}) G)"
(* "finite (possible_allocations_rel G (N-{n}))" (*MC: qv allocs_finite *) *)
"finite a" (*MC: the two finiteness requirements can be replaced by finiteness of N, G*)
"EX i. i\<in>Domain (a^-1 -- n) & b (i, (a^-1),,,i) \<le> b (i, (a^-1),,,i \<union> (a^-1),,,n)"
(* MC: this is monotonicity assumption *)
shows "Max (proceeds b ` (converse ` (possible_allocations_rel G (N - {n})))) \<ge> 
proceeds b ((a\<inverse>) -- n)"
proof -
  let ?P=possible_allocations_rel let ?aa="a^-1 -- n" let ?d=Domain let ?Yn="a^-1,,,n"
  let ?p=proceeds let ?X="converse ` (?P G (N-{n}))" let ?u=runiq let ?r=Range 

  have "?u a & ?u (a^-1)" using assms(1) lll81 by blast
  then moreover have "?u ?aa" using subrel_runiq Outside_def by blast
  moreover have "?aa \<subseteq> a^-1" using Outside_def by blast
  then moreover have "?aa^-1 \<subseteq> a" using Outside_def converse_def by (metis converse_subset_swap)
  ultimately have 
  2: "?u ?aa & ?u a & ?u (a^-1) & ?u (?aa^-1)" using subrel_runiq by auto obtain i where 
  0: "i \<in> ?d ?aa & b (i, (a^-1),,,i) \<le> b (i, (a^-1),,,i \<union> ?Yn)" using assms(5) by blast
  let ?Y1="?aa,,,i" let ?Y2="?Y1 \<union> ?Yn"
  
  have "{i} \<inter> {n}={}" using 0 by (metis Diff_iff Int_commute Int_empty_right Int_insert_right_if0 outside_reduces_domain)
  then have "?aa``{i} = (a^-1)``{i}" using 0 Outside_def Image_def lll86 by metis then
  have 
  7: "?Y1=(a^-1),,,i" by simp

  have 
  5: "?d ?aa \<subseteq> N - {n}" using assms lll81 by (metis Diff_mono Range_converse converse_converse outside_reduces_domain subset_refl)
  then have 
  6: "N - {n} \<union> {i} = N -{n}" using 0 by blast
  have
  3: "(?d a) partitions G" using assms lll81 by blast then
  have "is_partition (?r (a^-1))" using is_partition_of_def by (metis Range_converse)
  then have 
  4: "is_partition (?r ?aa)" using all_partitions_def is_partition_of_def 
  Outside_def subset_is_partition lll81 assms by (metis Range_outside_sub equalityE)
  moreover have "?Y1 \<in> (?r ?aa)" using 0 lll82 by (metis "2" eval_runiq_in_Range)
  ultimately have "?Y2 \<noteq> {}" using is_partition_def 0 by (metis Un_empty  inf_bot_right)

  have "{i} \<times> ?aa``{i} = {i} \<times> {?Y1}" using 0 Image_runiq_eq_eval 2 by (metis cSup_singleton)
  moreover have "... = {(i, ?Y1)}" by simp
  ultimately have 
  1: "?aa +< (i, ?Y1) = ?aa" using 0 paste_def eval_rel_def ll84 by (metis fst_conv snd_conv)
  
  have "?r (a^-1) = ?r ?aa \<union> ?r ((a^-1)||{n})" by (metis Range_Un_eq outside_union_restrict)
  moreover have "... = ?r ?aa \<union> (a^-1) `` {n}" by (metis lll85)
  ultimately moreover have "?r ?aa = (a^-1)``(?d (a^-1)-{n})" by (metis lll01 lll85)
  ultimately moreover have "?r (a^-1) = ?r ?aa \<union> (a^-1)``{n}" by simp
  ultimately moreover have "?r ?aa \<inter> (a^-1)``{n} = {}" using lll78
  by (metis "2" converse_converse)
  ultimately have "?r ?aa=?r (a^-1) - (a^-1)``{n}" by blast
  moreover have "a^-1``{n} = {?Yn}"
  by (metis "2" Domain_converse Image_runiq_eq_eval assms(2) lll82)
  ultimately have "?r ?aa = ?r (a^-1) - {?Yn}" by force
  moreover have "{?Yn} \<subseteq> ?r (a^-1)" using assms eval_runiq_in_Range by (metis "2" Domain_converse cSup_singleton empty_subsetI insert_subset runiq_wrt_eval_rel')
  moreover have "\<Union> (?r (a^-1))=G" using assms lll81 is_partition_of_def by (metis Range_converse)
  ultimately
  have "is_partition_of (?r ?aa) (G - ?Yn)" using lll80 3 2 4 
  by (metis `is_partition (Range (a\<inverse>))` cSup_singleton)
  moreover have "?u ?aa" by (metis "2")
  moreover have "?u (?aa^-1)" using 2 by fast
  moreover have "?d ?aa \<subseteq> (N -{n})" by (metis Diff_mono Domain_converse assms lll81 outside_reduces_domain subset_refl)

  ultimately have "?aa^-1 \<in> ?P (G-?Yn) (N-{n})" using assms lll81 by (metis Domain_converse converse_converse)

  moreover have "?Y2 \<inter> (G -?Yn - ?Y1)={}" by fast
  ultimately have "(?aa +< (i, ?Y2))\<inverse> \<in> ?P (G - ?Yn - ?Y1 \<union> ?Y2) (N-{n} \<union> {i})" 
  using lll74 by (metis `(a\<inverse> -- n) ,,, i \<union> a\<inverse> ,,, n \<noteq> {}`)
  then have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P (G \<union> ?Y2) (N-{n} \<union> {i})" by (smt Un_Diff_cancel Un_commute Un_left_commute)

  moreover have "?Yn \<subseteq> G"
  by (metis Union_upper `\<Union>Range (a\<inverse>) = G` `{a\<inverse> ,,, n} \<subseteq> Range (a\<inverse>)` insert_subset)
  moreover have "\<Union> (?r ?aa) \<subseteq> G"
  by (metis Diff_subset Sup_subset_mono `Range (a\<inverse> -- n) = Range (a\<inverse>) - {a\<inverse> ,,, n}` `\<Union>Range (a\<inverse>) = G`)
  then moreover have "?Y1 \<subseteq> G" 
  by (metis Sup_le_iff `(a\<inverse> -- n) ,,, i \<in> Range (a\<inverse> -- n)`)
  ultimately moreover have "?Y2 \<subseteq> G" by simp
  ultimately have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P G ((N-{n}) \<union> {i})" by (metis Un_absorb2)
  then have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P G (N-{n})" using 6 by force
  then have "?aa +< (i, ?Y2) \<in> ?X" by (metis converse_converse image_eqI)
  then have "?p b (?aa +< (i, ?Y2)) \<in> (?p b)`?X" by blast
  moreover have "finite (?p b ` ?X)" using assms(3) by (metis finite_imageI)
  ultimately have "?p b (?aa +< (i, ?Y2)) \<le> Max ((?p b) ` ?X)" using Max_ge by blast
  moreover have "b (i, ?Y1) \<le> b (i, ?Y2)" using 7 0 by presburger
  moreover have "finite ?aa" using assms(4) by (metis `a\<inverse> -- n \<subseteq> a\<inverse>` finite_converse finite_subset)
  ultimately moreover have " ?p b (?aa +< (i, ?Y2)) \<ge> ?p b (?aa +< (i, ?Y1))" using lll75
  by blast
  ultimately show ?thesis  using 1 by force
qed


corollary lm01:
assumes "a \<in> possibleAllocationsRel N G"
"n \<in> Domain a"
"finite (possibleAllocationsRel (N-{n}) G)" (*MC: qv allocs_finite *)
"finite a" (*MC: the two finiteness requirements can be replaced by finiteness of N, G*)
"EX i. i\<in>Domain (a -- n) & b (i, a,,,i) \<le> b (i, a,,,i \<union> a,,,n)"
(* MC: this is monotonicity assumption *)
shows "alpha N G b n \<ge> 
proceeds b (a -- n)" using lll76 assms converse_def 
proof -
  let ?p="possible_allocations_rel" let ?a="a^-1" let ?f=finite
  have "?a \<in> ?p G N" using assms by fastforce
  moreover have "n \<in> Range ?a" using assms
by fast
  moreover have "?f ?a" using assms by fast
  moreover have 
"EX i. i\<in>Domain (?a^-1 -- n) & b (i, (?a^-1),,,i) \<le> b (i, (?a^-1),,,i \<union> (?a^-1),,,n)"
using assms 
by simp
ultimately have 
"Max (proceeds b ` (converse ` (?p G (N - {n})))) \<ge> 
proceeds b ((?a\<inverse>) -- n)" using lll76 assms by blast
thus ?thesis by simp
qed

corollary lm08: assumes 
"a \<in> winningAllocationsRel N G b"
"n \<in> Domain a"
"finite (possibleAllocationsRel (N-{n}) G)"
"finite a"
"EX i. i\<in>Domain (a -- n) & b (i, a,,,i) \<le> b (i, a,,,i \<union> a,,,n)"
(* MC: this is monotonicity assumption *)
shows "alpha N G b n \<ge> 
proceeds b (a -- n)" using assms lm01 lm03 by simp

corollary assumes 
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))"
"n \<in> Domain (winningAllocationRel N G t b)" 
"finite (possibleAllocationsRel (N-{n}) G)"
"finite (winningAllocationRel N G t b)"
"EX i. i\<in>Domain ((winningAllocationRel N G t b) -- n) & 
b (i, (winningAllocationRel N G t b),,,i) \<le> 
b (i, (winningAllocationRel N G t b),,,i \<union> (winningAllocationRel N G t b),,,n)"
shows "alpha N G b n \<ge> remainingValueRel N G t b n"
using lm08 assms lm07 by blast
BIGSKIP *)

end

