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

header {* Sets of injections, partitions, allocations expressed as suitable subsets of the corresponding universes *}

theory Universes

imports 
"~~/src/HOL/Library/Code_Target_Nat"
StrictCombinatorialAuction 
"~~/src/HOL/Library/Indicator_Function"

begin

section {* Preliminary lemmas *}

lemma xm001: assumes "Y \<in> set (all_partitions_alg X)" shows "distinct Y"
using assms distinct_sorted_list_of_set all_partitions_alg_def all_partitions_equivalence'
by metis

(* This is a variant of the bridging theorem that the classical and constructive definitions of all_partitions characterize the same set *)
lemma xm002: assumes "finite G" 
            shows "all_partitions G  =  set ` (set (all_partitions_alg G))"
            using assms sortingSameSet all_partitions_alg_def all_partitions_paper_equiv_alg
                  distinct_sorted_list_of_set image_set by metis




section {* Definitions of various subsets of @{term UNIV}. *}

(* For with R = {({1,2},2), ({2,3},3)} is a choice relation, choosing one element of the set. *)
abbreviation "isChoice R == \<forall>x. R``{x} \<subseteq> x"
abbreviation "partitionsUniverse == {X. is_non_overlapping X}"
lemma "partitionsUniverse \<subseteq> Pow UNIV" 
      by simp       

abbreviation "partitionValuedUniverse == \<Union> P \<in> partitionsUniverse. Pow (UNIV \<times> P)"
lemma "partitionValuedUniverse \<subseteq> Pow (UNIV \<times> (Pow UNIV))" 
      by simp

abbreviation "injectionsUniverse == {R. (runiq R) & (runiq (R^-1))}"

(* allocations are injections so that goods are allocated at most once and the range from a partition of the goods. *)
abbreviation "allocationsUniverse == injectionsUniverse \<inter> partitionValuedUniverse"
abbreviation "totalRels X Y == {R. Domain R = X & Range R \<subseteq> Y}"




section {* Results about the sets defined in the previous section *}

lemma xm003: assumes "\<forall> x1 \<in> X. (x1 \<noteq> {} & (\<forall> x2 \<in> X-{x1}. x1 \<inter> x2  =  {}))" 
            shows "is_non_overlapping X" 
            unfolding is_non_overlapping_def using assms by fast

lemma xm004: assumes "\<forall>x \<in> X. f x \<in> x" 
            shows "isChoice (graph X f)" using assms
            by (metis Image_within_domain' empty_subsetI insert_subset graphEqImage domainOfGraph 
                      runiq_wrt_eval_rel subset_trans)

lemma xm005: "injections = injections'" using injections_def by (metis(no_types))
lemma xm006: "injections' X Y \<subseteq> injectionsUniverse" by fast
lemma xm007: "injections X Y \<subseteq> injectionsUniverse" using injections_def by blast
lemma xm008: "injections' X Y = totalRels X Y \<inter> injectionsUniverse" by fastforce

lemma allocationInverseRangeDomainProperty: assumes "a \<in> possibleAllocationsRel N G" 
            shows  "a^-1 \<in> injections (Range a) N & 
                    (Range a) partitions G & 
                    Domain a \<subseteq> N" 
            unfolding injections_def using assms all_partitions_def injections_def by fastforce

lemma xm009: assumes "is_non_overlapping XX" "YY \<subseteq> XX" 
             shows "(XX - YY) partitions (\<Union> XX - \<Union> YY)"
proof -
  let ?xx="XX - YY" let ?X="\<Union> XX" let ?Y="\<Union> YY"
  let ?x="?X - ?Y"
  have "\<forall> y \<in> YY. \<forall> x\<in>?xx. y \<inter> x={}" using assms is_non_overlapping_def by (metis Diff_iff set_rev_mp)
  then have "\<Union> ?xx \<subseteq> ?x" using assms by blast
  then have "\<Union> ?xx = ?x" by blast
  moreover have "is_non_overlapping ?xx" using subset_is_non_overlapping by (metis Diff_subset assms(1))
  ultimately
  show ?thesis using is_partition_of_def by blast
qed

lemma allocationRightUniqueRangeDomain: assumes "a \<in> possible_allocations_rel G N" 
              shows "runiq a & 
                     runiq (a\<inverse>) & 
                     (Domain a) partitions G & 
                     Range a \<subseteq> N" 
proof -
  obtain Y where
  0: "a \<in> injections Y N & Y \<in> all_partitions G" using assms possible_allocations_rel_def by auto
  show ?thesis using 0 injections_def all_partitions_def mem_Collect_eq by fastforce
qed

(* converse of the previous lemma *)
lemma xm010: assumes "runiq a" "runiq (a\<inverse>)" "(Domain a) partitions G" "Range a \<subseteq> N"
              shows "a \<in> possible_allocations_rel G N"
proof -
  have "a \<in> injections (Domain a) N" unfolding injections_def using assms(1) assms(2)  assms(4) by blast
  moreover have "Domain a \<in> all_partitions G" using assms(3) all_partitions_def by fast
  ultimately show ?thesis using assms(1) possible_allocations_rel_def by auto
qed

(* lemma allocationRightUniqueRangeDomain and xm010 combined *)
lemma allocationProperty: "a \<in> possible_allocations_rel G N \<longleftrightarrow>
                runiq a & runiq (a\<inverse>) & (Domain a) partitions G & Range a \<subseteq> N"
             using allocationRightUniqueRangeDomain xm010 by blast

lemma xm011: "possible_allocations_rel' G N \<subseteq> injectionsUniverse"
            using assms by force

lemma xm012: "possible_allocations_rel G N \<subseteq> {a. (Range a) \<subseteq> N & (Domain a) \<in> all_partitions G}"
            using assms possible_allocations_rel_def injections_def by fastforce

lemma xm013: "injections X Y = injections' X Y" 
            using injections_def by metis

lemma xm014: "all_partitions X = all_partitions' X" 
            using all_partitions_def is_partition_of_def by auto

lemma xm015: "possible_allocations_rel' A B  =  possible_allocations_rel A B" (is "?A=?B")
proof -
  have "?B=\<Union> { injections Y B | Y . Y \<in> all_partitions A }"
  using possible_allocations_rel_def by auto 
  moreover have "... = ?A" using injections_def xm014 by metis
  ultimately show ?thesis by presburger
qed

lemma xm016: "possible_allocations_rel G N \<subseteq> 
             injectionsUniverse \<inter> {a. Range a \<subseteq> N & Domain a \<in> all_partitions G}"
             using assms xm012 xm011 possible_allocations_rel_def injections_def by fastforce

lemma xm017: "possible_allocations_rel G N \<supseteq> 
             injectionsUniverse \<inter> {a. Domain a \<in> all_partitions G & Range a \<subseteq> N}"
            using possible_allocations_rel_def injections_def by auto

(* combination of the previous two lemmas *)
lemma xm018: "possible_allocations_rel G N   = 
             injectionsUniverse \<inter> {a. Domain a \<in> all_partitions G & Range a \<subseteq> N}"
             using xm016 xm017 by blast

(* all possible injections can be flipped and gives the same *)
lemma xm019: "converse ` injectionsUniverse = injectionsUniverse" 
            by auto

lemma xm020: "converse`(A \<inter> B)  =  (converse`A) \<inter> (converse`B)" 
            by force

lemma allocationInjectionsUnivervseProperty: "possibleAllocationsRel N G = 
             injectionsUniverse \<inter> {a. Domain a \<subseteq> N & Range a \<in> all_partitions G}"
proof -
  let ?A="possible_allocations_rel G N" let ?c=converse let ?I=injectionsUniverse 
  let ?P="all_partitions G" let ?d=Domain let ?r=Range
  have "?c`?A = (?c`?I) \<inter> ?c` ({a. ?r a \<subseteq> N & ?d a \<in> ?P})" using xm018 by fastforce
  moreover have "... = (?c`?I) \<inter> {aa. ?d aa \<subseteq> N & ?r aa \<in> ?P}" by fastforce
  moreover have "... = ?I \<inter> {aa. ?d aa \<subseteq> N & ?r aa \<in> ?P}" using xm019 by metis
  ultimately show ?thesis by presburger
qed

lemma xm021: "possibleAllocationsRel N G \<subseteq> injectionsUniverse" 
            using allocationInjectionsUnivervseProperty by fast

lemma xm022: "possibleAllocationsRel N G \<subseteq> partitionValuedUniverse"
            using assms allocationInverseRangeDomainProperty is_partition_of_def is_non_overlapping_def by blast

corollary possibleAllocationsUniverse: "possibleAllocationsRel N G \<subseteq> allocationsUniverse" 
                using xm021 xm022 by (metis (lifting, mono_tags) inf.bounded_iff)

corollary posssibleAllocationsRelCharacterization: "a \<in> possibleAllocationsRel N G = 
                  (a \<in> injectionsUniverse & Domain a \<subseteq> N & Range a \<in> all_partitions G)" 
                 using allocationInjectionsUnivervseProperty Int_Collect Int_iff by (metis (lifting))

corollary xm023: assumes "a \<in> possibleAllocationsRel N1 G" 
                 shows   "a \<in> possibleAllocationsRel (N1 \<union> N2) G"
proof - 
have "Domain a \<subseteq> N1 \<union> N2" using assms(1) posssibleAllocationsRelCharacterization by (metis le_supI1) 
moreover have "a \<in> injectionsUniverse & Range a \<in> all_partitions G" 
using assms posssibleAllocationsRelCharacterization by blast ultimately show ?thesis using posssibleAllocationsRelCharacterization by blast 
qed

corollary xm024: "possibleAllocationsRel N1 G \<subseteq> possibleAllocationsRel (N1 \<union> N2) G"
                 using xm023 by (metis subsetI)

lemma xm025: assumes "(\<Union> P1) \<inter> (\<Union> P2) = {}" 
                     "is_non_overlapping P1" "is_non_overlapping P2" 
                     "X \<in> P1 \<union> P2" "Y \<in> P1 \<union> P2" "X \<inter> Y \<noteq> {}" 
             shows "(X = Y)" 
             unfolding is_non_overlapping_def using assms is_non_overlapping_def by fast

lemma xm026: assumes "(\<Union> P1) \<inter> (\<Union> P2) = {}" 
                     "is_non_overlapping P1" "is_non_overlapping P2" 
                     "X \<in> P1 \<union> P2" "Y \<in> P1 \<union> P2" "(X = Y)" 
             shows "X \<inter> Y \<noteq> {}" 
             unfolding is_non_overlapping_def using assms is_non_overlapping_def by fast

lemma xm027:  assumes "(\<Union> P1) \<inter> (\<Union> P2) = {}" "is_non_overlapping P1" "is_non_overlapping P2"
             shows "is_non_overlapping (P1 \<union> P2)" 
             unfolding is_non_overlapping_def using assms xm025 xm026 by metis

lemma xm028: "Range Q \<union> (Range (P outside (Domain Q))) = Range (P +* Q)"
            unfolding paste_def Range_Un_eq Un_commute by (metis(no_types))

lemma xm029: assumes "a1 \<in> injectionsUniverse" "a2 \<in> injectionsUniverse" 
                      "(Range a1) \<inter> (Range a2)={}" "(Domain a1) \<inter> (Domain a2) = {}" 
              shows "a1 \<union> a2 \<in> injectionsUniverse" 
              using assms disj_Un_runiq 
              by (metis (no_types) Domain_converse converse_Un mem_Collect_eq)

lemma nonOverlapping:  assumes "R \<in> partitionValuedUniverse" 
             shows "is_non_overlapping (Range R)"
proof -
  obtain P where
  0: "P \<in> partitionsUniverse & R \<subseteq> UNIV \<times> P" using assms by blast
  have "Range R \<subseteq> P" using 0 by fast
  then show ?thesis using 0 mem_Collect_eq subset_is_non_overlapping by (metis)
qed

lemma allocationUnion: assumes "a1 \<in> allocationsUniverse" "a2 \<in> allocationsUniverse" 
                    "(\<Union> (Range a1)) \<inter> (\<Union> (Range a2)) = {}"
                    "(Domain a1) \<inter> (Domain a2) = {}" 
            shows "a1 \<union> a2 \<in> allocationsUniverse"
proof -
  let ?a="a1 \<union> a2" let ?b1="a1^-1" let ?b2="a2^-1" let ?r=Range let ?d=Domain
  let ?I=injectionsUniverse let ?P=partitionsUniverse let ?PV=partitionValuedUniverse let ?u=runiq
  let ?b="?a^-1" let ?p=is_non_overlapping
  have "?p (?r a1) & ?p (?r a2)" using assms nonOverlapping by blast then
  moreover have "?p (?r a1 \<union> ?r a2)" using assms by (metis xm027)
  then moreover have "(?r a1 \<union> ?r a2) \<in> ?P" by simp
  moreover have "?r ?a = (?r a1 \<union> ?r a2)" using assms by fast
  ultimately moreover have "?p (?r ?a)" using xm027 assms by fastforce
  then moreover have "?a \<in> ?PV" using assms by fast
  moreover have "?r a1 \<inter> (?r a2) \<subseteq> Pow (\<Union> (?r a1) \<inter> (\<Union> (?r a2)))" by auto
  ultimately moreover have "{} \<notin> (?r a1) & {} \<notin> (?r a2)" using is_non_overlapping_def by (metis Int_empty_left)
  ultimately moreover have "?r a1 \<inter> (?r a2) = {}" using assms nonOverlapping is_non_overlapping_def by auto
  ultimately moreover have "?a \<in> ?I" using xm029 assms by fastforce
  ultimately show ?thesis by blast
qed

(* - stands here for set difference *)
lemma xm030: assumes "a \<in> injectionsUniverse" 
            shows "a - b \<in> injectionsUniverse" 
            using assms 
            by (metis (lifting) Diff_subset converse_mono mem_Collect_eq subrel_runiq)

(* Note that -` is the inverse image of a lambda function. *)
lemma xm031: "{a. Domain a \<subseteq> N    &   Range a \<in> all_partitions G} =
              (Domain -`(Pow N))  \<inter>  (Range -` (all_partitions G)) " 
             by fastforce

lemma xm032: "possibleAllocationsRel N G = 
             injectionsUniverse \<inter> ((Range -` (all_partitions G)) \<inter> (Domain -`(Pow N)))"
             using allocationInjectionsUnivervseProperty xm031 by (metis (no_types) Int_commute)

(* -` is the reverse image of a function. This is a variant of xm023 with different bracketing *)
corollary xm033: "possibleAllocationsRel N G = 
                 injectionsUniverse \<inter> (Range -` (all_partitions G)) \<inter> (Domain -`(Pow N))" 
                using xm032 Int_assoc 
                by (metis)

lemma xm034: assumes "a \<in> possibleAllocationsRel N G" 
             shows "(a^-1 \<in> injections (Range a) N & 
                    Range a \<in> all_partitions G)"
             using assms 
             by (metis (mono_tags, hide_lams) posssibleAllocationsRelCharacterization allocationInverseRangeDomainProperty)

lemma xm035: assumes "a^-1 \<in> injections (Range a) N" "Range a \<in> all_partitions G" 
             shows "a \<in> possibleAllocationsRel N G" 
             using assms image_iff by fastforce

lemma allocationReverseInjective: "a \<in> possibleAllocationsRel N G = 
            (a^-1 \<in> injections (Range a) N  &  Range a \<in> all_partitions G)"
            using xm034 xm035 
            by metis

lemma xm036: assumes "a \<in> possibleAllocationsRel N G" 
             shows "a \<in> injections (Domain a) (Range a) & 
                    Range a \<in> all_partitions G &
                    Domain a \<subseteq> N"
             using assms mem_Collect_eq injections_def posssibleAllocationsRelCharacterization order_refl 
             by (metis (mono_tags, lifting))

lemma xm037: assumes "a \<in> injections (Domain a) (Range a)" 
                     "Range a \<in> all_partitions G" "Domain a \<subseteq> N" 
             shows "a \<in> possibleAllocationsRel N G" 
             using assms mem_Collect_eq posssibleAllocationsRelCharacterization injections_def 
             by (metis (erased, lifting))

lemma characterizationPossibleAllocationsRel: "a \<in> possibleAllocationsRel N G = 
             (a \<in> injections (Domain a) (Range a)  & 
              Range a \<in> all_partitions G & 
              Domain a \<subseteq> N)" 
            using xm036 xm037 
            by metis

lemma xm038: assumes "a \<in> partitionValuedUniverse" 
            shows "a - b \<in> partitionValuedUniverse" 
            using assms subset_is_non_overlapping 
            by fast

lemma reducedAllocation: assumes "a \<in> allocationsUniverse" 
            shows "a - b \<in> allocationsUniverse" 
            using assms xm030 xm038 
            by auto

lemma xm039: assumes "a \<in> injectionsUniverse" 
            shows "a \<in> injections (Domain a) (Range a)"
            using assms injections_def mem_Collect_eq order_refl 
            by blast

lemma xm040: assumes "a \<in> allocationsUniverse" 
            shows "a \<in> possibleAllocationsRel (Domain a) (\<Union> (Range a))"
proof -
let ?r=Range let ?p=is_non_overlapping let ?P=all_partitions have "?p (?r a)" using 
assms nonOverlapping Int_iff by blast then have "?r a \<in> ?P (\<Union> (?r a))" unfolding all_partitions_def 
using is_partition_of_def  mem_Collect_eq by (metis) then show ?thesis using 
assms IntI Int_lower1 equalityE allocationInjectionsUnivervseProperty mem_Collect_eq set_rev_mp by (metis (lifting, no_types))
qed

lemma xm041: "({X} \<in> partitionsUniverse) = (X \<noteq> {})" 
            using is_non_overlapping_def 
            by fastforce

lemma xm042: "{(x, X)} - {(x, {})} \<in> partitionValuedUniverse" 
             using xm041 
             by auto

lemma singlePairInInjectionsUniverse: "{(x, X)} \<in> injectionsUniverse" 
            unfolding runiq_basic using runiq_singleton_rel 
            by blast

lemma allocationUniverseProperty: "{(x,X)} - {(x,{})} \<in> allocationsUniverse" 
             using xm042 singlePairInInjectionsUniverse xm030 Int_iff 
             by (metis (no_types))

(* PP is a family of partitions *)
lemma xm043: assumes "is_non_overlapping PP" "is_non_overlapping (Union PP)" 
            shows "is_non_overlapping (Union ` PP)"
proof -
let ?p=is_non_overlapping let ?U=Union let ?P2="?U PP" let ?P1="?U ` PP" have 
0: "\<forall> X\<in>?P1. \<forall> Y \<in> ?P1. (X \<inter> Y = {} \<longrightarrow> X \<noteq> Y)" using assms is_non_overlapping_def Int_absorb 
Int_empty_left UnionI Union_disjoint ex_in_conv imageE by (metis (hide_lams, no_types))
{
  fix X Y assume 
  2: "X \<in> ?P1 & Y\<in>?P1 & X \<noteq> Y"
  then obtain XX YY where 
  1: "X = ?U XX & Y=?U YY & XX\<in>PP & YY\<in>PP" by blast
  then have "XX \<subseteq> Union PP & YY \<subseteq> Union PP & XX \<inter> YY = {}" 
  using 2 1 is_non_overlapping_def assms(1) Sup_upper by metis
  then moreover have "\<forall> x\<in>XX. \<forall> y\<in>YY. x \<inter> y = {}" using 1 assms(2) is_non_overlapping_def 
by (metis IntI empty_iff subsetCE)
  ultimately have "X \<inter> Y={}" using assms 0 1 2 is_non_overlapping_def by auto
}
then show ?thesis using 0 is_non_overlapping_def by metis
qed

(* A preservation of reallocating goods of the participants in X to a single participant i. *)
lemma xm044: assumes "a \<in> allocationsUniverse" 
            shows "(a - ((X\<union>{i})\<times>(Range a))) \<union> 
                   ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allocationsUniverse & 
                   \<Union> (Range ((a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) =
                   \<Union>(Range a)"
proof -
  let ?d=Domain let ?r=Range let ?U=Union let ?p=is_non_overlapping let ?P=partitionsUniverse let ?u=runiq 
  let ?Xi="X \<union> {i}" let ?b="?Xi \<times> (?r a)" let ?a1="a - ?b" let ?Yi="a``?Xi" let ?Y="?U ?Yi" 
  let ?A2="{(i, ?Y)}" let ?a3="{(i,{})}" let ?a2="?A2 - ?a3" let ?aa1="a outside ?Xi" 
  let ?c="?a1 \<union> ?a2" let ?t1="?c \<in> allocationsUniverse" have 
  7: "?U(?r(?a1\<union>?a2))=?U(?r ?a1) \<union> (?U(?r ?a2))" by (metis Range_Un_eq Union_Un_distrib) have 
  5: "?U(?r a) \<subseteq> ?U(?r ?a1) \<union> ?U(a``?Xi) & ?U(?r ?a1) \<union> ?U(?r ?a2) \<subseteq> ?U(?r a)" by blast have
  1: "?u a & ?u (a^-1) & ?p (?r a) & ?r ?a1 \<subseteq> ?r a & ?Yi \<subseteq> ?r a" 
  using assms Int_iff nonOverlapping mem_Collect_eq by auto then have 
  2: "?p (?r ?a1) & ?p ?Yi" using subset_is_non_overlapping by metis have 
  "?a1 \<in> allocationsUniverse & ?a2 \<in> allocationsUniverse" using allocationUniverseProperty assms(1) reducedAllocation by fastforce then have 
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
    moreover have "?Yi \<inter> (a``(?d a - ?Xi)) = {}" using assms 0 1 
    Diff_disjoint intersectionEmptyRelationIntersectionEmpty by metis
    ultimately moreover have "?r ?a1 \<inter> ?Yi = {} & ?Yi \<noteq> {}" by blast
    ultimately moreover have "?p {?r ?a1, ?Yi}" unfolding is_non_overlapping_def using  
IntI Int_commute empty_iff insert_iff subsetI subset_empty by metis
    moreover have "?U {?r ?a1, ?Yi} \<subseteq> ?r a" by auto
    then moreover have "?p (?U {?r ?a1, ?Yi})" by (metis "1" Outside_def subset_is_non_overlapping)
    ultimately moreover have "?p (?U`{(?r ?a1), ?Yi})" using xm043 by fast
    moreover have "... = {?U (?r ?a1), ?Y}" by force
    ultimately moreover have "\<forall> x \<in> ?r ?a1. \<forall> y\<in>?Yi. x \<noteq> y" 
    using IntI empty_iff by metis
    ultimately moreover have "\<forall> x \<in> ?r ?a1. \<forall> y\<in>?Yi. x \<inter> y = {}" using 0 1 2 is_non_overlapping_def
    by (metis set_rev_mp)
    ultimately have "?U (?r ?a1) \<inter> ?Y = {}" using unionIntersectionEmpty
proof -
  have "\<forall>v0. v0 \<in> Range (a - (X \<union> {i}) \<times> Range a) \<longrightarrow> (\<forall>v1. v1 \<in> a `` (X \<union> {i}) \<longrightarrow> v0 \<inter> v1 = {})" 
by (metis (no_types) `\<forall>x\<in>Range (a - (X \<union> {i}) \<times> Range a). \<forall>y\<in>a \`\` (X \<union> {i}). x \<inter> y = {}`) 
  thus "\<Union>Range (a - (X \<union> {i}) \<times> Range a) \<inter> \<Union>(a `` (X \<union> {i})) = {}" by blast
qed then have 
    "?U (?r ?a1) \<inter> (?U (?r ?a2)) = {}" by blast
    moreover have "?d ?a1 \<inter> (?d ?a2) = {}" by blast
    moreover have "?a1 \<in> allocationsUniverse" using assms(1) reducedAllocation by blast
    moreover have "?a2 \<in> allocationsUniverse" using allocationUniverseProperty by fastforce
    ultimately have "?a1 \<in> allocationsUniverse & 
    ?a2 \<in> allocationsUniverse &
    \<Union>Range ?a1 \<inter> \<Union>Range ?a2 = {} & Domain ?a1 \<inter> Domain ?a2 = {}" 
by blast then have 
?t1 using allocationUnion by auto       
    then have ?thesis using 6 7 by presburger
  }
  then show ?thesis using 3 by linarith
qed

corollary allocationsUniverseOutsideUnion: assumes "a \<in> allocationsUniverse" 
                 shows   "(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) 
                                \<in> allocationsUniverse & 
                          \<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})))) = 
                          \<Union>(Range a)"
proof -
have "a - ((X\<union>{i})\<times>(Range a)) = a outside (X \<union> {i})" using Outside_def by metis
moreover have "(a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allocationsUniverse"
using assms xm044 by fastforce
moreover have "\<Union> (Range ((a - ((X\<union>{i})\<times>(Range a))) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)"
using assms xm044 by (metis (no_types))
ultimately have
"(a outside (X\<union>{i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) \<in> allocationsUniverse & 
\<Union> (Range ((a outside (X\<union>{i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}))) = \<Union>(Range a)" by
presburger
moreover have "{(i, \<Union> (a``(X \<union> {i})))} - {(i,{})} = {i} \<times> ({\<Union> (a``(X\<union>{i}))} - {{}})" 
by fast
ultimately show ?thesis by auto
qed

(* If there is an allocation with a participant in its domain, then the goods allocated are non-empty *)
lemma xm045: assumes "Domain a \<inter> X \<noteq> {}" "a \<in> allocationsUniverse" 
            shows   "\<Union>(a``X) \<noteq> {}"
proof -
  let ?p=is_non_overlapping let ?r=Range
  have "?p (?r a)" using assms Int_iff nonOverlapping by auto
  moreover have "a``X \<subseteq> ?r a" by fast
  ultimately have "?p (a``X)" using assms subset_is_non_overlapping by blast
  moreover have "a``X \<noteq> {}" using assms by fast
  ultimately show ?thesis by (metis Union_member all_not_in_conv no_empty_in_non_overlapping)
qed

(* i is an additional bidder added to X *)
corollary xm058: assumes "Domain a \<inter> X \<noteq> {}" "a \<in> allocationsUniverse" 
                 shows   "{\<Union>(a``(X\<union>{i}))}-{{}}  =  {\<Union>(a``(X\<union>{i}))}" 
                 using assms xm045 by fast

(* variant of 43b *)
corollary xm059: assumes "a \<in> allocationsUniverse" "(Domain a) \<inter> X \<noteq> {}" 
                 shows   "(a outside (X\<union>{i})) \<union> ({i}\<times>{\<Union>(a``(X\<union>{i}))}) \<in> allocationsUniverse & 
                         \<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>{\<Union>(a``(X\<union>{i}))}))) = \<Union>(Range a)"
proof -
let ?t1="(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> allocationsUniverse"
let ?t2="\<Union>(Range((a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})))) = \<Union>(Range a)"
have 
0: "a \<in> allocationsUniverse" using assms(1) by fast 
then have "?t1 & ?t2" using allocationsUniverseOutsideUnion 
proof - 
  have "a \<in> allocationsUniverse \<longrightarrow> a outside (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allocationsUniverse"
    using allocationsUniverseOutsideUnion by fastforce
  hence "a outside (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allocationsUniverse"
    by (metis "0")
  thus "a outside (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}}) \<in> allocationsUniverse \<and> \<Union>Range (a outside (X \<union> {i}) \<union> {i} \<times> ({\<Union>(a `` (X \<union> {i}))} - {{}})) = \<Union>Range a"
    using "0" by (metis (no_types) allocationsUniverseOutsideUnion)
qed
moreover have 
1: "{\<Union>(a``(X\<union>{i}))}-{{}} = {\<Union>(a``(X\<union>{i}))}" using xm045 assms by fast
ultimately show ?thesis by auto
qed

(* The bid vector does not decrease when you bid for extra goods *)
abbreviation "bidMonotonicity b i == (\<forall> t t'. (trivial t & trivial t' & Union t \<subseteq> Union t') \<longrightarrow>
setsum b ({i}\<times>t) \<le> setsum b ({i}\<times>t'))" 

(* adding the goods in X weakly increases the revenue *)
lemma xm046: assumes "bidMonotonicity b i" "runiq a" 
            shows  "setsum b ({i}\<times>((a outside X)``{i})) \<le> setsum b ({i}\<times>{\<Union>(a``(X\<union>{i}))})"
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

lemma xm047:  assumes "XX \<in> partitionValuedUniverse" 
             shows "{} \<notin> Range XX" 
             using assms mem_Collect_eq no_empty_in_non_overlapping by auto

corollary emptyNotInRange: assumes "a \<in> possibleAllocationsRel N G" 
                 shows "{} \<notin> Range a" 
                 using assms xm047 possibleAllocationsUniverse by blast

lemma xm048: assumes "a \<in> possibleAllocationsRel N G" 
            shows "Range a \<subseteq> Pow G"
            using assms allocationInverseRangeDomainProperty is_partition_of_def by (metis subset_Pow_Union)

corollary xm049: assumes "a \<in> possibleAllocationsRel N G" 
                 shows "Domain a \<subseteq> N & Range a \<subseteq> Pow G - {{}}" 
                 using assms xm048 insert_Diff_single emptyNotInRange subset_insert allocationInverseRangeDomainProperty by metis

corollary allocationPowerset: assumes "a \<in> possibleAllocationsRel N G" 
                 shows "a \<subseteq> N \<times> (Pow G - {{}})" 
                 using assms xm049 by blast

corollary xm050: "possibleAllocationsRel N G \<subseteq> Pow (N\<times>(Pow G-{{}}))" 
                 using allocationPowerset by blast

(* reformulation of 43c with given set of goods and set of participants *)
lemma xm051: assumes  "a \<in> possibleAllocationsRel N G" 
                     "i \<in> N-X" 
                     "Domain a \<inter> X \<noteq> {}" 
            shows   "a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))}) \<in> 
                     possibleAllocationsRel (N-X) (\<Union> (Range a))"
proof -
  let ?R="a outside X" let ?I="{i}" let ?U=Union let ?u=runiq let ?r=Range let ?d=Domain
  let ?aa="a outside (X \<union> {i}) \<union> ({i} \<times> {?U(a``(X\<union>{i}))})" have 
  1: "a \<in> allocationsUniverse" using assms(1) possibleAllocationsUniverse  set_rev_mp by blast
  have "i \<notin> X" using assms by fast then have 
  2: "?d a - X \<union> {i} = ?d a \<union> {i} - X" by fast
  have "a \<in> allocationsUniverse" using 1 by fast moreover have "?d a \<inter> X \<noteq> {}" using assms by fast 
  ultimately have "?aa \<in> allocationsUniverse & ?U (?r ?aa) = ?U (?r a)" apply (rule xm059) done
  then have "?aa \<in> possibleAllocationsRel (?d ?aa) (?U (?r a))"
using xm040 by (metis (lifting, mono_tags))
then have "?aa \<in> possibleAllocationsRel (?d ?aa \<union> (?d a - X \<union> {i}))  (?U (?r a))"
by (metis xm023)
  moreover have "?d a - X \<union> {i} = ?d ?aa \<union> (?d a - X \<union> {i})" using Outside_def by auto
  ultimately have "?aa \<in> possibleAllocationsRel (?d a - X \<union> {i}) (?U (?r a))" by simp
  then have "?aa \<in> possibleAllocationsRel (?d a \<union> {i} - X) (?U (?r a))" using 2 by simp
  moreover have "?d a \<subseteq> N" using assms(1) posssibleAllocationsRelCharacterization by metis
  then moreover have "(?d a \<union> {i} - X) \<union> (N - X) = N - X" using assms by fast
  ultimately have "?aa \<in> possibleAllocationsRel (N - X) (?U (?r a))" using xm024 
  by (metis (lifting, no_types) in_mono)
  then show ?thesis by fast
qed

lemma xm060: assumes "bidMonotonicity (b::_ => real) i" 
                    "a \<in> allocationsUniverse" 
                    "Domain a \<inter> X \<noteq> {}" 
                    "finite a"
            shows   "setsum b (a outside X) \<le> 
                     setsum b (a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))}))"
proof -
  let ?R="a outside X" let ?I="{i}" let ?U=Union let ?u=runiq let ?r=Range let ?d=Domain
  let ?aa="a outside (X \<union> {i}) \<union> ({i} \<times> {?U(a``(X\<union>{i}))})"
  have "a \<in> injectionsUniverse" using assms by fast then have 
  0: "?u a" by simp
  moreover have "?R \<subseteq> a & ?R--i \<subseteq> a" using Outside_def by blast
  ultimately have "finite (?R -- i) & ?u (?R--i) & ?u ?R" using finite_subset subrel_runiq
  by (metis assms(4))
  then moreover have "trivial ({i}\<times>(?R``{i}))" using runiq_def 
  by (metis trivial_cartesian trivial_singleton)
  moreover have "\<forall>X. (?R -- i) \<inter> ({i}\<times>X)={}" using outside_reduces_domain by force
  ultimately have 
  1: "finite (?R--i) & finite ({i}\<times>(?R``{i})) & (?R -- i) \<inter> ({i}\<times>(?R``{i}))={} & 
  finite ({i} \<times> {?U(a``(X\<union>{i}))}) & (?R -- i) \<inter> ({i} \<times> {?U(a``(X\<union>{i}))})={}" 
  using Outside_def trivial_implies_finite by fast 
  have "?R = (?R -- i) \<union> ({i}\<times>?R``{i})" by (metis outsideUnion)
  then have "setsum b ?R = setsum b (?R -- i) + setsum b ({i}\<times>(?R``{i}))" 
  using 1 setsum.union_disjoint by (metis (lifting) setsum.union_disjoint)
  moreover have "setsum b ({i}\<times>(?R``{i})) \<le> setsum b ({i}\<times>{?U(a``(X\<union>{i}))})" using xm046 
  assms(1) 0 by metis
  ultimately have "setsum b ?R \<le> setsum b (?R -- i) + setsum b ({i}\<times>{?U(a``(X\<union>{i}))})" by linarith
  moreover have "... = setsum b (?R -- i \<union> ({i} \<times> {?U(a``(X\<union>{i}))}))" 
  using 1 setsum.union_disjoint by auto
  moreover have "... = setsum b ?aa" by (metis outsideOutside)
  ultimately show ?thesis by linarith
qed

lemma elementOfPartitionOfFiniteSetIsFinite: assumes "finite X" "XX \<in> all_partitions X" 
            shows "finite XX" 
            using all_partitions_def is_partition_of_def 
            by (metis assms(1) assms(2) finite_UnionD mem_Collect_eq)

lemma xm070: assumes "finite N" "finite G" "a \<in> possibleAllocationsRel N G"
            shows "finite a" 
            using assms finiteRelationCharacterization rev_finite_subset by (metis characterizationPossibleAllocationsRel elementOfPartitionOfFiniteSetIsFinite)

lemma possibleAllocationsRelFinite: assumes "finite N" "finite G" 
            shows "finite (possibleAllocationsRel N G)"
proof -
  have "finite (Pow(N\<times>(Pow G-{{}})))" using assms finite_Pow_iff by blast
  then show ?thesis using xm050 rev_finite_subset by (metis(no_types))
qed

corollary xm072: assumes "bidMonotonicity (b::_ => real) i" 
                        "a \<in> possibleAllocationsRel N G" 
                        "i \<in> N-X" 
                        "Domain a \<inter> X \<noteq> {}" 
                        "finite N" 
                        "finite G" 
                shows   "Max ((setsum b)`(possibleAllocationsRel (N-X) G)) \<ge> 
                         setsum b (a outside X)"
proof -
  let ?aa="a outside (X \<union> {i}) \<union> ({i} \<times> {\<Union>(a``(X\<union>{i}))})"
  have "bidMonotonicity (b::_ => real) i" using assms(1) by fast
  moreover have "a \<in> allocationsUniverse" using assms(2) possibleAllocationsUniverse by blast
  moreover have "Domain a \<inter> X \<noteq> {}" using assms(4) by auto
  moreover have "finite a" using assms xm070 by metis ultimately have 
  0: "setsum b (a outside X) \<le> setsum b ?aa" by (rule xm060)
  have "?aa \<in> possibleAllocationsRel (N-X) (\<Union> (Range a))" using assms xm051 by metis
  moreover have "\<Union> (Range a) = G" using assms allocationInverseRangeDomainProperty is_partition_of_def by metis
  ultimately have "setsum b ?aa \<in> (setsum b)`(possibleAllocationsRel (N-X) G)" by (metis imageI)
  moreover have "finite ((setsum b)`(possibleAllocationsRel (N-X) G))" using assms possibleAllocationsRelFinite assms(5,6)
  by (metis finite_Diff finite_imageI)
  ultimately have "setsum b ?aa \<le> Max ((setsum b)`(possibleAllocationsRel (N-X) G))" by auto
  then show ?thesis using 0 by linarith
qed

lemma cardinalityPreservation: assumes "finite XX" "\<forall>X \<in> XX. finite X" "is_non_overlapping XX" 
            shows   "card (\<Union> XX) = setsum card XX" 
            using assms is_non_overlapping_def card_Union_disjoint by fast

corollary cardSetsumCommute: assumes "XX partitions X" "finite X" "finite XX" 
                 shows   "card (\<Union> XX) = setsum card XX" 
                 using assms cardinalityPreservation by (metis is_partition_of_def familyUnionFiniteEverySetFinite)

(* \<Sigma>_x\<in> (Union C) (f x)   is the same as \<Sigma>_x\<in> C (\<Sigma>_set\<in> C (\<Sigma>_x\<in>set (f x))) *)
lemma setsumUnionDisjoint1: assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A Int B = {}" 
                            shows "setsum f (Union C) = setsum (setsum f) C" 
                            using assms setsum.Union_disjoint by fastforce

corollary setsumUnionDisjoint2: assumes "\<forall>x\<in>X. finite x" "is_non_overlapping X" 
                                shows "setsum f (\<Union> X) = setsum (setsum f) X" 
                                using assms setsumUnionDisjoint1 is_non_overlapping_def 
                                by fast

corollary setsumUnionDisjoint3: assumes "\<forall>x\<in>X. finite x" "X partitions XX" 
                                shows "setsum f XX = setsum (setsum f) X" 
                                using assms 
                                by (metis is_partition_of_def setsumUnionDisjoint2)

corollary setsum_associativity: assumes "finite x" "X partitions x" 
                                shows  "setsum f x = setsum (setsum f) X" 
                                using assms setsumUnionDisjoint3 
                                by (metis is_partition_of_def familyUnionFiniteEverySetFinite)

lemma xm074: assumes "a \<in> allocationsUniverse" "Domain a \<subseteq> N" "(\<Union>Range a) = G" 
             shows   "a \<in> possibleAllocationsRel N G" 
             using assms posssibleAllocationsRelCharacterization xm040 by (metis (mono_tags, lifting))

corollary xm075: "(allocationsUniverse \<inter> {a. (Domain a) \<subseteq> N & (\<Union>Range a) = G}) \<subseteq>
                  possibleAllocationsRel N G"
          using xm074 by fastforce

corollary xm076: "possibleAllocationsRel N G \<subseteq> {a. (Domain a) \<subseteq> N}" 
          using allocationInverseRangeDomainProperty by blast

corollary xm077: "possibleAllocationsRel N G \<subseteq> {a. (\<Union>Range a) = G}" 
          using is_partition_of_def allocationInverseRangeDomainProperty mem_Collect_eq subsetI
          by (metis(mono_tags))

corollary xm078: "possibleAllocationsRel N G  \<subseteq>  allocationsUniverse &
                  possibleAllocationsRel N G \<subseteq> {a. (Domain a) \<subseteq> N & (\<Union>Range a) = G}" 
                  using xm076 xm077 conj_subset_def possibleAllocationsUniverse by (metis (no_types))

corollary possibleAllocationsIntersectionSubset: "possibleAllocationsRel N G \<subseteq> 
                  allocationsUniverse \<inter> {a. (Domain a) \<subseteq> N & (\<Union>Range a) = G}"
                 (is "?L \<subseteq> ?R1 \<inter> ?R2")
proof - 
  have "?L \<subseteq> ?R1 & ?L \<subseteq> ?R2" by (rule xm078) thus ?thesis by auto 
qed

corollary possibleAllocationsIntersection: "possibleAllocationsRel N G = 
                (allocationsUniverse \<inter> {a. (Domain a) \<subseteq> N & (\<Union>Range a) = G})" 
                (is "?L = ?R") 
proof -
  have "?L \<subseteq> ?R" using possibleAllocationsIntersectionSubset by metis moreover have "?R \<subseteq> ?L" using xm075 by fast
  ultimately show ?thesis by force
qed

corollary possibleAllocationsIntersectionSetEquals: "a \<in> possibleAllocationsRel N G  = 
                  (a \<in> allocationsUniverse  & (Domain a) \<subseteq> N & (\<Union>Range a) = G)" 
                 using possibleAllocationsIntersection Int_Collect by (metis (mono_tags, lifting))

corollary allocationsUniverseOutside: assumes "a \<in> allocationsUniverse" 
                 shows "a outside X \<in> allocationsUniverse" 
                 using assms Outside_def by (metis (lifting, mono_tags) reducedAllocation)


section{* Bridging theorem for injections *}

lemma xm083: "totalRels {} Y = {{}}" 
            by fast

lemma xm084: "{} \<in> injectionsUniverse" 
            by (metis CollectI converse_empty runiq_emptyrel)

lemma xm085: "injectionsUniverse \<inter> (totalRels {} Y)  =  {{}}" 
            using xm083 xm084 by fast

lemma xm086: assumes "runiq f" "x\<notin>Domain f" 
            shows "{ f \<union> {(x, y)} | y . y \<in> A } \<subseteq> runiqs" 
            unfolding paste_def runiqs_def
            using assms runiq_basic by blast

lemma xm087: "converse ` (converse ` X)  =  X" 
            by auto

lemma xm088: "runiq (f^-1) = (f \<in> converse`runiqs)" 
            unfolding runiqs_def by auto

lemma xm089: assumes "runiq (f^-1)" "A \<inter> Range f  =  {}" 
            shows   "converse ` { f \<union> {(x, y)} | y . y \<in> A } \<subseteq> runiqs" 
            using assms xm086 by fast

lemma xm090: assumes "f\<in>converse`runiqs" "A \<inter> Range f  =  {}" 
             shows   "{f \<union> {(x, y)}| y. y \<in> A} \<subseteq> converse`runiqs" 
             (is "?l \<subseteq> ?r")
proof -
  have "runiq (f^-1)" using assms(1) xm088 by blast then
  have "converse ` ?l \<subseteq> runiqs" using assms(2) by (rule xm089) 
  then have "?r \<supseteq> converse`(converse`?l)" by auto
  moreover have "converse`(converse`?l)=?l" by (rule xm087)
  ultimately show ?thesis by simp
qed

lemma xm091: "{ R \<union> {(x, y)} | y . y \<in> A } \<subseteq> totalRels ({x} \<union> Domain R) (A \<union> Range R)" 
            by force

lemma xm092: "injectionsUniverse  =  runiqs \<inter> converse`runiqs" 
            unfolding runiqs_def by auto

lemma xm093: assumes "f \<in> injectionsUniverse" "x \<notin> Domain f" "A \<inter> (Range f) = {}" 
            shows   "{f \<union> {(x, y)}| y. y \<in> A} \<subseteq> injectionsUniverse" 
            (is "?l \<subseteq> ?r") 
proof -  
  have "f \<in> converse`runiqs" using assms(1) xm092 by blast
  then have "?l \<subseteq> converse`runiqs" using assms(3) by (rule xm090)
  moreover have "?l \<subseteq> runiqs" using assms(1,2) xm086 by force 
  ultimately show ?thesis using xm092 by blast
qed

lemma xm094: "injections X Y = totalRels X Y \<inter> injectionsUniverse" 
             using injections_def xm008 by metis

lemma xm095: assumes "f \<in> injectionsUniverse" 
             shows   "f outside A \<in> injectionsUniverse" 
             using assms by (metis (no_types) Outside_def xm030)

lemma xm096: assumes "R \<in> totalRels A B" 
            shows   "R outside C \<in> totalRels (A-C) B" 
            unfolding Outside_def using assms by blast

lemma xm097: assumes "g \<in> injections' A B" 
            shows   "g outside C \<in> injections' (A - C) B" 
            using assms Outside_def Range_outside_sub xm030 mem_Collect_eq outside_reduces_domain
            by fastforce

lemma xm098: assumes "g \<in> injections A B" 
             shows   "g outside C \<in> injections (A - C) B"
             using assms xm097 by (metis injections_def)

lemma xm099: "{x}\<times>{y}={(x,y)}" 
            by simp

lemma xm100: assumes "x \<in> Domain f" "runiq f" 
            shows "{x}\<times>f``{x} = {(x,f,,x)}" 
            using assms xm099 Image_runiq_eq_eval by metis

corollary xm101: assumes "x \<in> Domain f" "runiq f" 
                shows   "f = (f -- x) \<union> {(x,f,,x)}" 
                using assms xm100 outsideUnion by metis

lemma xm102: assumes "f \<in> injectionsUniverse" 
             shows   "Range(f outside A) = Range f - f``A" 
             using assms mem_Collect_eq rangeOutside by (metis)

lemma xm103: assumes "g \<in> injections' X Y" "x \<in> Domain g" 
            shows   "g \<in> {g--x \<union> {(x,y)}|y. y \<in> Y - (Range(g--x))}" 
proof - 
  let ?f="g--x" have "g\<in>injectionsUniverse" using assms(1) xm008 by fast then moreover have 
  "g,,x \<in> g``{x}" using assms(2) by (metis Image_runiq_eq_eval insertI1 mem_Collect_eq)
  ultimately have "g,,x \<in> Y-Range ?f" using xm102 assms(1) by fast moreover have "g=?f\<union>{(x, g,,x)}" 
  using assms xm101 mem_Collect_eq by (metis (lifting)) ultimately show ?thesis by blast 
qed

corollary xm104: assumes "x \<notin> X" "g \<in> injections ({x} \<union> X) Y" 
                 shows "g--x \<in> injections X Y" 
                 using assms xm098 by (metis Diff_insert_absorb insert_is_Un)

corollary xm105: assumes "x \<notin> X" "g \<in> injections ({x} \<union> X) Y" 
                        (is "g \<in> injections (?X) Y") 
                shows   "\<exists> f \<in> injections X Y. g \<in> {f \<union> {(x,y)}|y. y \<in> Y - (Range f)}" 
proof - 
  let ?f="g--x" have 1: "g\<in>injections' ?X Y" using assms Universes.xm005 by metis 
  have "Domain g=?X" using assms(2) Universes.xm005 mem_Collect_eq by (metis (mono_tags, lifting))
  then have 0: "x \<in> Domain g" by simp then have "?f \<in> injections X Y" using assms xm104 by fast
  moreover have "g\<in>{?f\<union>{(x,y)}|y. y\<in>Y-Range ?f}" using 1 0 by (rule xm103)
  ultimately show ?thesis by blast
qed

corollary xm106: assumes "x \<notin> X" 
                 shows  "injections ({x} \<union> X) Y \<subseteq> 
                         (\<Union> f \<in> injections X Y. {f \<union> {(x, y)} | y . y \<in> Y - (Range f)})"
                 using assms xm105 by fast

lemma xm107: assumes "x \<notin> X" 
             shows  "(\<Union> f\<in>injections' X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f}) \<subseteq> 
                     injections' ({x} \<union> X) Y" 
             using assms xm093 injections_def xm094 xm091 
proof -
  { fix f assume "f \<in> injections' X Y" then have 
  0: "f \<in> injectionsUniverse & x \<notin> Domain f & Domain f = X & Range f \<subseteq> Y" using assms by fast 
  then have "f \<in> injectionsUniverse" by fast moreover have "x \<notin> Domain f" using 0 by fast
  moreover have 1: "(Y-Range f) \<inter> Range f = {}" by blast
  ultimately have "{f \<union> {(x, y)} | y . y \<in> (Y-Range f)} \<subseteq> injectionsUniverse" by (rule xm093)
  moreover have "{f \<union> {(x, y)} | y . y \<in> (Y-Range f)} \<subseteq> totalRels ({x} \<union> X) Y" using xm091 0 by force
  ultimately have "{f \<union> {(x, y)} | y . y \<in> (Y-Range f)} \<subseteq> injectionsUniverse \<inter> totalRels ({x}\<union>X) Y" by auto}
  thus ?thesis using xm008 by blast
qed

corollary injectionsUnionCommute: assumes "x \<notin> X" 
                shows   "(\<Union> f\<in>injections X Y. {f \<union> {(x, y)} | y . y \<in> Y - (Range f)}) = 
                         injections ({x} \<union> X) Y" 
                (is "?r=injections ?X _") 
proof - 
  have 
  0: "?r=(\<Union> f\<in>injections' X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f})" (is "_=?r'") unfolding xm005 by blast 
  have "?r' \<subseteq> injections' ?X Y" using assms by (rule xm107) moreover have "... = injections ?X Y" unfolding xm005 
  by simp ultimately have "?r \<subseteq> injections ?X Y" using 0 by simp
  moreover have "injections ?X Y \<subseteq> ?r" using assms by (rule xm106) ultimately show ?thesis by blast
qed

lemma xm109: assumes "\<forall> x. (P x \<longrightarrow> (f x = g x))" 
            shows   "Union {f x|x. P x} = Union {g x | x. P x}" 
            using assms try0 by blast

lemma xm110: assumes "x \<notin> Domain R" 
            shows "R +* {(x,y)} = R \<union> {(x,y)}" 
            using assms
            by (metis (erased, lifting) Domain_empty Domain_insert Int_insert_right_if0
                      disjoint_iff_not_equal ex_in_conv paste_disj_domains)

(* Union of {f ...} where f ranges over injections X Y *)
lemma xm111: assumes "x \<notin> X" 
            shows "(\<Union> f \<in> injections X Y. {f +* {(x, y)} | y . y \<in> Y-Range f}) = 
                   (\<Union> f \<in> injections X Y. {f \<union>  {(x, y)}  | y . y \<in> Y-Range f})" 
            (is "?l = ?r") 
proof - 
  have 
  0: "\<forall>f \<in> injections X Y. x \<notin> Domain f" unfolding injections_def using assms by fast then have 
  1: "?l=Union {{f +* {(x, y)} | y . y \<in> Y-Range f}|f .f \<in> injections X Y & x \<notin> Domain f}" 
  (is "_=?l'") using assms by auto moreover have 
  2: "?r=Union {{f \<union> {(x, y)} | y . y \<in> Y-Range f}|f .f \<in> injections X Y & x \<notin> Domain f}" 
  (is "_=?r'") using assms 0 by auto have "\<forall> f. f\<in>injections X Y & x \<notin> Domain f \<longrightarrow> 
  {f +* {(x, y)} | y . y \<in> Y-Range f}={f \<union> {(x, y)} | y . y \<in> Y-Range f}" using xm110 by force 
  then have "?l'=?r'" by (rule xm109) then show "?l = ?r" using 1 2 by presburger
qed

corollary xm112: assumes "x \<notin> X" 
                 shows   "(\<Union> f \<in> injections X Y. {f +* {(x, y)} | y . y \<in> Y-Range f}) = 
                          injections ({x} \<union> X) Y" 
                 (is "?l=?r")
proof - 
  have "?l=(\<Union> f\<in>injections X Y. {f \<union> {(x, y)} | y . y \<in> Y-Range f})" using assms by (rule xm111)
  moreover have "... = ?r" using assms by (rule injectionsUnionCommute) ultimately show ?thesis by presburger 
qed

lemma xm113: "set [ f \<union> {(x,y)} . y \<leftarrow> (filter (%y. y \<notin> (Range f)) Y) ] = 
                  {f \<union> {(x,y)} | y . y \<in> (set Y) -     (Range f)}" 
             by auto

(* relationship of list and set notation for function application *)
lemma xm114: assumes "\<forall>x \<in> set L. set (F x) = G x" 
            shows "set (concat [ F x . x <- L]) = (\<Union> x\<in>set L. G x)"
            using assms by force

(* relationship of list and set notation for function extension *)
lemma xm115: "set (concat [ [ f \<union> {(x,y)} . y \<leftarrow> (filter (%y. y \<notin> Range f) Y) ]. f \<leftarrow> F ]) =
             (\<Union> f \<in> set F. {f \<union> {(x,y)} | y . y \<in> (set Y) - (Range f)})" 
            by auto

(* relationship of list vs set comprehension versions of function update*)
lemma xm116: assumes "finite Y" 
             shows   "set [ f +* {(x,y)} . y \<leftarrow> sorted_list_of_set (Y - (Range f)) ] =
                     {      f +* {(x,y)} | y . y \<in>                 Y - (Range f)}" 
             using assms by auto

lemma xm117: assumes "finite Y" 
             shows "set (concat [[f +* {(x,y)}. y \<leftarrow> sorted_list_of_set(Y - (Range f))]. f \<leftarrow> F]) =
                   (\<Union> f \<in> set F.{f +* {(x,y)} | y . y \<in> Y - (Range f)})" 
             using assms xm116 xm114 by auto

section{* computable injections *}

fun injectionsAlg 
    where 
    "injectionsAlg [] (Y::'a list) = [{}]" |
    "injectionsAlg (x#xs) Y = 
       concat [ [R\<union>{(x,y)}. y \<leftarrow> (filter (%y. y \<notin> Range R) Y)]
               .R \<leftarrow> injectionsAlg xs Y ]"

corollary xm118: "set (injectionsAlg (x # xs) Y) = 
                 (\<Union> f \<in> set (injectionsAlg xs Y). {f \<union> {(x,y)} | y . y \<in> (set Y) - (Range f)})" 
                 using xm115 injectionsAlg_def by auto

corollary xm119: assumes "set (injectionsAlg xs Y) = injections (set xs) (set Y)" 
                 shows   "set (injectionsAlg (x # xs) Y) = 
                        (\<Union> f \<in> injections (set xs) (set Y). {f \<union> {(x,y)} | y . y \<in> (set Y) - (Range f)})" 
                 using assms xm118 by auto

text{* We sometimes use parallel @{term abbreviation} and @{term definition} for the same object to save typing `unfolding xxx' each time. There is also different behaviour in the code extraction. *}

lemma xm120:  "injections' {} Y  =  {{}}" 
             by (simp add: xm008 xm083 runiq_emptyrel)

lemma xm121: "injections {} Y  =  {{}}" 
             unfolding injections_def by (simp add: xm008 xm083 runiq_emptyrel) 

lemma injectionsFromEmptyIsEmpty: "injectionsAlg [] Y  =  [{}]" 
            using injectionsAlg_def by simp

(* Relation between classical and algorithm definition of injections for induction step *)
lemma xm123: assumes "x \<notin> set xs" "set (injectionsAlg xs Y) = injections (set xs) (set Y)" 
            shows   "set (injectionsAlg (x # xs) Y) = injections ({x} \<union> set xs) (set Y)" 
            (is "?l=?r")
proof - 
  have "?l = (\<Union> f\<in>injections (set xs) (set Y). {f \<union> {(x,y)} | y . y \<in> (set Y)-Range f})" 
  using assms(2) by (rule xm119) moreover have "... = ?r" using assms(1) by (rule injectionsUnionCommute) 
  ultimately show ?thesis by presburger
qed

lemma xm124: assumes "x \<notin> set xs" 
                     "set (injections_alg xs Y) = injections (set xs) Y" 
                     "finite Y" 
            shows    "set (injections_alg (x#xs) Y) = injections ({x} \<union> set xs) Y" 
            (is "?l=?r")
proof - 
  have "?l = (\<Union> f\<in>injections (set xs) Y. {f +* {(x,y)} | y . y \<in> Y-Range f})" 
  using assms(2,3) xm117 by auto
  moreover have "... = ?r" using assms(1) by (rule xm112) 
  ultimately show ?thesis by presburger
qed

lemma listInduct: assumes "P []" "\<forall> xs x. P xs \<longrightarrow> P (x#xs)" 
                  shows   "\<forall>x. P x"
                  using assms by (metis structInduct)

lemma injectionsFromEmptyAreEmpty: "set (injections_alg [] Z) = {{}}" 
            by simp

theorem injections_equiv: assumes "finite Y" and "distinct X" 
                          shows  "set (injections_alg X Y) = injections (set X) Y"
proof -
  let ?P="\<lambda> l. (distinct l \<longrightarrow> (set (injections_alg l Y)=injections (set l) Y))"
  have "?P []" using injectionsFromEmptyAreEmpty list.set(1) xm121 by (metis)
  moreover have "\<forall>x xs. ?P xs \<longrightarrow> ?P (x#xs)" using assms(1) xm124 by (metis distinct.simps(2) list.simps(15))
  ultimately have "?P X" by (rule structInduct)
  then show ?thesis using assms(2) by blast
qed


lemma xm125: assumes "l \<in> set (all_partitions_list G)" "distinct G" 
            shows   "distinct l" 
            using assms all_partitions_list_def by (metis all_partitions_equivalence')

(* apply bridging theorem injections_equiv to the partitions of all goods *)
lemma bridgingInjection: assumes "card N > 0" "distinct G" 
            shows "\<forall>l \<in> set (all_partitions_list G). set (injections_alg l N) = 
                   injections (set l) N"
            using xm125 injections_equiv assms by (metis card_ge_0_finite)

(* list vs set comprehension on partitions with bridging theorem *)
lemma xm127: assumes "card N > 0" "distinct G"
            shows "{injections P N| P. P \<in> all_partitions (set G)} =
                   set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G]" 
proof -
  let ?g1=all_partitions_list let ?f2=injections let ?g2=injections_alg
  have "\<forall>l \<in> set (?g1 G). set (?g2 l N) = ?f2 (set l) N" using assms bridgingInjection by blast
  then have "set [set (?g2 l N). l <- ?g1 G] = {?f2 P N| P. P \<in> set (map set (?g1 G))}" apply (rule setVsList) done
  moreover have "... = {?f2 P N| P. P \<in> all_partitions (set G)}" using all_partitions_paper_equiv_alg
  assms by blast
  ultimately show ?thesis by presburger
qed

(* apply Union to both sides in xm127 *)
lemma xm128: assumes "card N > 0" "distinct G" 
            shows   "Union {injections P N| P. P \<in> all_partitions (set G)} =
                     Union (set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G])" 
            (is "Union ?L = Union ?R")
proof - 
  have "?L = ?R" using assms by (rule xm127) thus ?thesis by presburger 
qed

(* bridging lemma for possibleAllocations *)
corollary possibleAllocationsBridgingLemma: assumes "card N > 0" "distinct G" 
                 shows   "possibleAllocationsRel N (set G) = 
                          set(possibleAllocationsAlg N G)" 
proof -
  let ?LL="\<Union> {injections P N| P. P \<in> all_partitions (set G)}"
  let ?RR="\<Union> (set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G])"
  have "?LL = ?RR" using assms apply (rule xm128) done
  then have "converse ` ?LL = converse ` ?RR" by presburger
  thus ?thesis using possible_allocations_rel_def by force
qed

end

