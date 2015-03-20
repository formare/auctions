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

header {* Termination theorem for uniform tie-breaking *}

theory UniformTieBreaking

imports 
StrictCombinatorialAuction
Universes
"~~/src/HOL/Library/Code_Target_Nat"

begin


section {* Uniform tie breaking: definitions *}
text{* Let us repeat the general context. Each bidder has made their bids and the VCG algorithm up
 to now allocates goods to the higher bidders. If there are several high bidders tie breaking has 
to take place. To do tie breaking we generate out of a random number a second bid vector so that 
the same algorithm can be run again to determine a unique allocation.

To this end, we associate to each allocation the bid in which each participant bids for a set 
of goods an amount equal to the cardinality of the intersection of the bid with the set 
she gets in this allocation.
By construction, the revenue of an auction run using this bid is maximal on the given allocation,
and this maximal is unique.
We can then use the bid constructed this way @{term tiebids'} to break ties by running an auction 
having the same form as a normal auction (that is why we use the adjective ``uniform''), 
only with this special bid vector. *}

(* omega pair is a tool to compute cardinalities of pairs, e.g. for a pair made of a participant 1 and a set of goods {11,12,13}, the result will be the set of pairs: {(1,{11}), (1,{12}), (1,{13})}.
*)
abbreviation "omega pair == {fst pair} \<times> (finestpart (snd pair))"

(* pseudo allocation is like an allocation, but without uniqueness of the elements allocated *)
definition "pseudoAllocation allocation == \<Union> (omega ` allocation)"

(* some abbreviation to defined tiebids below *)
abbreviation "bidMaximizedBy allocation N G == 
              pseudoAllocation allocation <|| ((N \<times> (finestpart G)))"
(* functional version of the above *)
abbreviation "maxbid' a N G == 
              toFunction (bidMaximizedBy a N G)"

(* For bidding the cardinality of the second element of a single pair, i.e.,
   (bidder, goods) \<rightarrow> ((bidder, goods), bid) *)
abbreviation "summedBid bids pair == 
              (pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))"

(* returns just the bid in the above *)
abbreviation "summedBidSecond bids pair == 
              setsum (%g. bids (fst pair, g)) (finestpart (snd pair))"

(* apply summedBid to each possible pair *)
abbreviation "summedBidVectorRel bids N G == (summedBid bids) ` (N \<times> (Pow G - {{}}))"

(* functional version of above *)
abbreviation "summedBidVector' bids N G == toFunction (summedBidVectorRel bids N G)"

(* tiebids returns a bid vector that when the VCG algorithm runs on it yields the singleton {allocation}. Functional version *)
abbreviation "tiebids' allocation N G == summedBidVector' (maxbid' allocation N G) N G"

(* relational version of the above *)
abbreviation "Tiebids allocation N G == summedBidVectorRel (real\<circ>maxbid' allocation N G) N G"

(* the chosen allocation takes the random-th element of all possible winning allocations. This is done by taking the head of permuting the list random-times. The definition is easier for proving theorems. Since it is not the computational version, this inefficiency is irrelevant for the extracted code. *)
abbreviation "chosenAllocation' N G bids random == 
   hd(perm2 (takeAll (%x. x\<in>(winningAllocationsRel N (set G) bids)) 
                     (possibleAllocationsAlg N G)) 
            (nat_of_integer random))"

(* find the bid vector in random values that returns the chosen winning allocation *)
abbreviation "resolvingBid' N G bids random == 
  tiebids' (chosenAllocation' N G bids random) N (set G)"



section {* Termination theorem for the uniform tie-breaking scheme @{term resolvingBid'} *}

corollary lm03: 
  "winningAllocationsRel N G b \<subseteq> possibleAllocationsRel N G" 
  using injectionsFromEmptyAreEmpty mem_Collect_eq subsetI by auto

lemma lm35b: 
  assumes "a \<in> allocationsUniverse" "c \<subseteq> a" 
  shows "c \<in> allocationsUniverse"  
proof - 
  have "c=a-(a-c)" using assms(2) by blast 
  thus ?thesis using assms(1) lm35 by (metis (no_types)) 
qed

lemma lm35c: 
  assumes "a \<in> allocationsUniverse" 
  shows "a outside X \<in> allocationsUniverse"
  using assms lm35 Outside_def by (metis (no_types))

corollary lm38d: 
  "{x}\<times>({X}-{{}}) \<in> allocationsUniverse" 
  using allocationUniverseProperty pairDifference by metis

(* TPTP? *)
corollary lm38b: 
  "{(x,{y})} \<in> allocationsUniverse" 
proof -
  have "\<And>x1. {} - {x1\<Colon>'a \<times> 'b set} = {}" by simp
  thus "{(x, {y})} \<in> allocationsUniverse" 
  by (metis (no_types) allocationUniverseProperty empty_iff insert_Diff_if insert_iff prod.inject)
qed

corollary lm38c: 
  "allocationsUniverse \<noteq> {}" 
  using lm38b by fast

corollary 
  nn39: "{} \<in> allocationsUniverse" 
  using lm35b lm38b by (metis (lifting, mono_tags) empty_subsetI)

lemma lm87: 
  assumes "G \<noteq> {}" 
  shows "{G} \<in> all_partitions G" 
  using all_partitions_def is_partition_of_def is_non_overlapping_def assms by force

lemma lm88: 
  assumes "n \<in> N" 
  shows "{(G,n)} \<in> totalRels {G} N" 
  using assms by force

lemma lm89: 
  assumes "n\<in>N" 
  shows "{(G,n)} \<in> injections {G} N" 
  using assms injections_def lm37 by fastforce

corollary lm90: 
  assumes " G\<noteq>{}" "n\<in>N" 
  shows "{(G,n)} \<in> possible_allocations_rel G N"
proof -
  have "{(G,n)} \<in> injections {G} N" using assms lm89 by fast
  moreover have "{G} \<in> all_partitions G" using assms lm87 by metis
  ultimately show ?thesis using possible_allocations_rel_def by auto
qed

corollary lm90b: 
  assumes "N \<noteq> {}" "G\<noteq>{}" 
  shows "possibleAllocationsRel N G \<noteq> {}"
  using assms lm90 
  by (metis (hide_lams, no_types) equals0I image_insert insert_absorb insert_not_empty)

corollary lm91: 
  assumes "N \<noteq> {}" "finite N" "G \<noteq> {}" "finite G" 
  shows "winningAllocationsRel N G bids \<noteq> {} & finite (winningAllocationsRel N G bids)" 
  using assms lm90b lm59 argmax_non_empty_iff by (metis lm03 rev_finite_subset)

lemma lm52: 
  "possibleAllocationsRel N {} \<subseteq> {{}}" 
  using emptyset_part_emptyset3 rangeEmpty lm28b mem_Collect_eq subsetI vimage_def by metis

lemma lm42: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "finite (Range a)" 
  using assms lm55 by (metis lm28)

corollary lm44: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "finite a"
  using assms finite_converse Range_converse imageE lll81 finiteDomainImpliesFinite lm42
  by (metis (erased, lifting))

lemma lm41: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "\<forall> y \<in> Range a. finite y" 
  using assms is_partition_of_def lm47 by (metis Union_upper rev_finite_subset)

(* Note that allocations are strict, that is, all goods are allocated to the bidders at this point. Later we will have the seller as participant 0 getting all goods not allocated *)
corollary lm33c: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "card G = setsum card (Range a)" 
  using assms lm33b lm42 lm47 by (metis is_partition_of_def)



section{* Results on summed bid vectors *}

lemma lm66: 
  "summedBidVectorRel bids N G = 
   {(pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))|
    pair. pair \<in> N \<times> (Pow G-{{}})}" 
  by blast

(* Note that || stands for restriction, here to an allocation a *)
corollary lm65b: 
  "{(pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
    pair. pair \<in> (N \<times> (Pow G-{{}})) } || a = 
   {(pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
    pair. pair \<in> (N \<times> (Pow G-{{}}))   \<inter>  a}"
  by (metis restrictionVsIntersection)

corollary lm66b: 
  "(summedBidVectorRel bids N G) || a = 
   {(pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
    pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
   (is "?L = ?R")
proof -
  let ?l = summedBidVectorRel
  let ?M = "{(pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
             pair. pair \<in> N \<times> (Pow G-{{}})}"
  have "?l bids N G = ?M" by (rule lm66)
  then have "?L = (?M || a)" by presburger
  moreover have "... = ?R" by (rule lm65b)
  ultimately show ?thesis by simp
qed

lemma lm66c: 
  "(summedBid bids) ` ((N \<times> (Pow G - {{}})) \<inter> a) = 
   {(pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair))) | 
    pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
  by blast

corollary lm66d: 
  "(summedBidVectorRel bids N G) || a = (summedBid bids) ` ((N \<times> (Pow G - {{}})) \<inter> a)"
  (is "?L=?R")
proof -
  let ?l=summedBidVectorRel 
  let ?p=summedBid 
  let ?M="{(pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
           pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
  have "?L = ?M" by (rule lm66b)
  moreover have "... = ?R" using lm66c by blast
  ultimately show ?thesis by simp
qed

(* the function made by (summedBid bids) is always injective, that is, also with domain UNIV *)
lemma lm57: 
  "inj_on (summedBid bids) UNIV" 
  using assms fst_conv inj_on_inverseI by (metis (lifting)) 

(* restrict above to any set X *)
corollary lm57b: 
  "inj_on (summedBid bids) X" 
  using fst_conv inj_on_inverseI by (metis (lifting))

(* relationship between different formalizations of summedBid *)
lemma lm58: 
  "setsum snd (summedBidVectorRel bids N G) = 
   setsum (snd \<circ> (summedBid bids)) (N \<times> (Pow G - {{}}))" 
  using assms lm57b setsum.reindex by blast 

(* remember: omega of (1,{11,12,13}) is {(1,{11}), (1,{12}), (1,{13})} *)
corollary lm25: 
  "snd (summedBid bids pair) = setsum bids (omega pair)" 
  using sumCurry by force

(* restatement of the above *)
corollary lm25b: 
  "snd \<circ> summedBid bids = (setsum bids) \<circ> omega" 
  using lm25 by fastforce

lemma lm27: 
  assumes "finite  (finestpart (snd pair))" 
  shows "card (omega pair) = card (finestpart (snd pair))" 
  using assms by force

corollary 
  assumes "finite (snd pair)" 
  shows "card (omega pair) = card (snd pair)" 
  using assms cardFinestpart card_cartesian_product_singleton by metis

lemma lm30: 
  assumes "{} \<notin> Range f" "runiq f"
  shows "is_non_overlapping (omega ` f)"
proof -
let ?X="omega ` f" let ?p=finestpart
  { fix y1 y2; 
    assume "y1 \<in> ?X & y2 \<in> ?X"
    then obtain pair1 pair2 where 
      "y1 = omega pair1 & y2 = omega pair2 & pair1 \<in> f & pair2 \<in> f" by blast
    then moreover have "snd pair1 \<noteq> {} & snd pair1 \<noteq> {}" 
      using assms by (metis rev_image_eqI snd_eq_Range)
    ultimately moreover have "fst pair1 = fst pair2 \<longleftrightarrow> pair1 = pair2" 
      using assms runiq_basic surjective_pairing by metis
    ultimately moreover have "y1 \<inter> y2 \<noteq> {} \<longrightarrow> y1 = y2" using assms by fast
    ultimately have "y1 = y2 \<longleftrightarrow> y1 \<inter> y2 \<noteq> {}" 
      using assms notEmptyFinestpart by (metis Int_absorb Times_empty insert_not_empty)
    }
  thus ?thesis using is_non_overlapping_def 
    by (metis (lifting, no_types) inf_commute inf_sup_aci(1))
qed

lemma lm32: 
  assumes "{} \<notin> Range X" 
  shows "inj_on omega X"
proof -
  let ?p=finestpart
  {
    fix pair1 pair2 
    assume "pair1 \<in> X & pair2 \<in> X" 
    then have "snd pair1 \<noteq> {} & snd pair2 \<noteq> {}" 
      using assms by (metis Range.intros surjective_pairing)
    moreover assume "omega pair1 = omega pair2" 
    then moreover have "?p (snd pair1) = ?p (snd pair2)" by blast
    then moreover have "snd pair1 = snd pair2" by (metis finestPart nonEqualitySetOfSets)
    ultimately moreover have "{fst pair1} = {fst pair2}" using notEmptyFinestpart 
      by (metis fst_image_times)
    ultimately have "pair1 = pair2" by (metis prod_eqI singleton_inject)
  }
  thus ?thesis by (metis (lifting, no_types) inj_onI)
qed

lemma lm36: 
  assumes "{} \<notin> Range a" "finite (omega ` a)" "\<forall>X \<in> omega ` a. finite X" 
          "is_non_overlapping (omega ` a)"
  shows "card (pseudoAllocation a) = setsum (card \<circ> omega) a" 
  (is "?L = ?R")
proof -
  have "?L = setsum card (omega ` a)" 
  unfolding pseudoAllocation_def
  using assms(2,3,4) by (rule cardinalityPreservation)
  moreover have "... = ?R" using assms(1) lm32 setsum.reindex by blast
  ultimately show ?thesis by simp
qed

lemma lm39: 
  "card (omega pair)= card (snd pair)" 
  using cardFinestpart card_cartesian_product_singleton by metis

corollary lm39b: 
  "card \<circ> omega = card \<circ> snd" 
  using lm39 by fastforce

(* set image of omega on a set of pair is called pseudoAllocation *)
corollary lm37: 
  assumes "{} \<notin> Range a" "\<forall> pair \<in> a. finite (snd pair)" "finite a" "runiq a" 
  shows "card (pseudoAllocation a) = setsum (card \<circ> snd) a"
proof -
  let ?P=pseudoAllocation 
  let ?c=card
  have "\<forall> pair \<in> a. finite (omega pair)" using finiteFinestpart assms by blast 
  moreover have "is_non_overlapping (omega ` a)" using assms lm30 by force 
  ultimately have "?c (?P a) = setsum (?c \<circ> omega) a" using assms lm36 by force
  moreover have "... = setsum (?c \<circ> snd) a" using lm39b by metis
  ultimately show ?thesis by simp
qed

corollary lm46: 
  assumes "runiq (a^-1)" "runiq a" "finite a" "{} \<notin> Range a" "\<forall> pair \<in> a. finite (snd pair)" 
  shows "card (pseudoAllocation a) = setsum card (Range a)" 
  using assms setsumPairsInverse lm37 by force

corollary lm48: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "card (pseudoAllocation a) = card G"
proof -
  have "{} \<notin> Range a" using assms by (metis Universes.lm39b)
  moreover have "\<forall> pair \<in> a. finite (snd pair)" using assms lm41 finitePairSecondRange by metis
  moreover have "finite a" using assms lm44 by blast
  moreover have "runiq a" using assms by (metis (lifting) Int_lower1 in_mono lm19 mem_Collect_eq)
  moreover have "runiq (a^-1)" using assms 
                               by (metis (mono_tags) injections_def lm28b mem_Collect_eq)
  ultimately have "card (pseudoAllocation a) = setsum card (Range a)" using lm46 by fast
  moreover have "... = card G" using assms lm33c by metis
  ultimately show ?thesis by simp
qed

corollary lm49: 
  assumes "pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" 
          "finite (pseudoAllocation aa)"
  shows "setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation a) - 
            (setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation aa)) = 
         card (pseudoAllocation a) - 
            card (pseudoAllocation aa \<inter> (pseudoAllocation a))" 
  using assms subsetCardinality by blast

corollary lm49c: 
  assumes "pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" 
          "finite (pseudoAllocation aa)"
  shows "int (setsum (maxbid' a N G) (pseudoAllocation a)) - 
           int (setsum (maxbid' a N G) (pseudoAllocation aa)) = 
         int (card (pseudoAllocation a)) - 
           int (card (pseudoAllocation aa \<inter> (pseudoAllocation a)))" 
  using differenceSetsumVsCardinality assms by blast

lemma lm50: 
  "pseudoAllocation {} = {}" 
  unfolding pseudoAllocation_def by simp

corollary lm53b: 
  assumes "a \<in> possibleAllocationsRel N {}" 
  shows "(pseudoAllocation a) = {}"
  unfolding pseudoAllocation_def using assms lm52 by blast

corollary lm53: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" "G \<noteq> {}"
  shows "finite (pseudoAllocation a)" 
proof -
  have "card (pseudoAllocation a) = card G" using assms(1,2) lm48 by blast
  thus "finite (pseudoAllocation a)" using assms(2,3) by fastforce
qed

corollary lm54: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "finite (pseudoAllocation a)" 
  using assms finite.emptyI lm53 lm53b by (metis (no_types))

lemma lm56: 
  assumes "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G" "finite G" 
  shows  "(card (pseudoAllocation aa \<inter> (pseudoAllocation a)) = card (pseudoAllocation a)) = 
          (pseudoAllocation a = pseudoAllocation aa)" 
proof -
  let ?P=pseudoAllocation 
  let ?c=card 
  let ?A="?P a" 
  let ?AA="?P aa"
  have "?c ?A=?c G & ?c ?AA=?c G" using assms lm48 by (metis (lifting, mono_tags))
  moreover have "finite ?A & finite ?AA" using assms lm54 by blast
  ultimately show ?thesis using assms cardinalityIntersectionEquality by (metis(no_types,lifting))
qed

(* alternative definition for omega *)
lemma lm55: 
  "omega pair = {fst pair} \<times> {{y}| y. y \<in> snd pair}" 
  using finestpart_def finestPart by auto

(* variant of above *)
lemma lm55c: 
  "omega pair = {(fst pair, {y})| y. y \<in>  snd pair}" 
  using lm55 setOfPairs by metis

lemma lm55d: 
  "pseudoAllocation a = \<Union> {{(fst pair, {y})| y. y \<in> snd pair}| pair. pair \<in> a}"
  unfolding pseudoAllocation_def using lm55c by blast

lemma lm55e: 
  "\<Union> {{(fst pair, {y})| y. y \<in> snd pair}| pair. pair \<in> a} = 
   {(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}"
  by blast

corollary lm55k: 
  "pseudoAllocation a = {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a}"
  unfolding pseudoAllocation_def using setOfPairsEquality by fastforce

lemma lm55u: 
  assumes "runiq a" 
  shows "{(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a} = 
         {(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
         (is "?L=?R") 
  using assms Domain.DomainI fst_conv functionOnFirstEqualsSecond runiq_wrt_ex1 surjective_pairing
  by (metis(hide_lams,no_types))

corollary lm55v: 
  assumes "runiq a" 
  shows "pseudoAllocation a = {(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
  unfolding pseudoAllocation_def using assms lm55u lm55k by fastforce

corollary lm55t: 
  "Range (pseudoAllocation a) = \<Union> (finestpart ` (Range a))"
  unfolding pseudoAllocation_def
  using lm55k rangeSetOfPairs unionFinestPart  by fastforce

corollary lm55s: 
  "Range (pseudoAllocation a) = finestpart (\<Union> Range a)" 
  using commuteUnionFinestpart lm55t by metis 

lemma lm55f: 
  "pseudoAllocation a = {(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" 
  using lm55d lm55e by (metis (full_types))

lemma lm55g: 
  "{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a} = 
   {(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a}"
   by auto

lemma lm55i: 
  "pseudoAllocation a = {(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a}"
  (is "?L=?R")
proof -
  have "?L={(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" by (rule lm55f)
  moreover have "... = ?R" by (rule lm55g) 
  ultimately show ?thesis by simp
qed

lemma lm62: 
  "runiq (summedBidVectorRel bids N G)" 
  using assms graph_def image_Collect_mem domainOfGraph by (metis(no_types))

corollary lm62b: 
  "runiq (summedBidVectorRel bids N G || a)"
  unfolding restrict_def using lm62 subrel_runiq Int_commute by blast

lemma lm64: 
  "N \<times> (Pow G - {{}}) = Domain (summedBidVectorRel bids N G)" 
  by blast

corollary lm63d: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "a \<subseteq> Domain (summedBidVectorRel bids N G)"
proof -
  let ?p=possibleAllocationsRel 
  let ?L=summedBidVectorRel
  have "a \<subseteq> N \<times> (Pow G - {{}})" using assms Universes.lm40c by (metis(no_types))
  moreover have "N \<times> (Pow G - {{}}) = Domain (?L bids N G)" using lm64 by blast
  ultimately show ?thesis by blast
qed

corollary lm59d: 
  "setsum (summedBidVector' bids N G) (a \<inter> (Domain (summedBidVectorRel bids N G))) = 
   setsum snd ((summedBidVectorRel bids N G) || a)" 
  using assms setsumRestrictedToDomainInvariant lm62b by fast

corollary lm59e: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "setsum (summedBidVector' bids N G) a = setsum snd ((summedBidVectorRel bids N G) || a)" 
proof -
  let ?l=summedBidVector' let ?L=summedBidVectorRel
  have "a \<subseteq> Domain (?L bids N G)" using assms by (rule lm63d) 
  then have "a = a \<inter> Domain (?L bids N G)" by blast 
  then have "setsum (?l bids N G) a = setsum (?l bids N G) (a \<inter> Domain (?L bids N G))" 
       by presburger
  thus ?thesis using lm59d by auto
qed

corollary lm59f: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "setsum (summedBidVector' bids N G) a = 
         setsum snd ((summedBid bids) ` ((N \<times> (Pow G - {{}})) \<inter> a))"
        (is "?X=?R")
proof -
  let ?p = summedBid 
  let ?L = summedBidVectorRel 
  let ?l = summedBidVector'
  let ?A = "N \<times> (Pow G - {{}})" 
  let ?inner2 = "(?p bids)`(?A \<inter> a)" 
  let ?inner1 = "(?L bids N G)||a"
  have "?R = setsum snd ?inner1" using assms lm66d by (metis (no_types))
  moreover have "setsum (?l bids N G) a = setsum snd ?inner1" using assms by (rule lm59e)
  ultimately show ?thesis by simp
qed

corollary lm59g: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "setsum (summedBidVector' bids N G) a = setsum snd ((summedBid bids) ` a)" 
  (is "?L=?R")
proof -
  let ?p=summedBid 
  let ?l=summedBidVector'
  have "?L = setsum snd ((?p bids)`((N \<times> (Pow G - {{}}))\<inter> a))" using assms by (rule lm59f)
  moreover have "... = ?R" using assms lm40c Int_absorb1 by (metis (no_types))
  ultimately show ?thesis by simp
qed

corollary lm57c: 
  "setsum snd ((summedBid bids) ` a) = setsum (snd \<circ> (summedBid bids)) a"
  using assms setsum.reindex lm57b by blast

corollary lm59h: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "setsum (summedBidVector' bids N G) a = setsum (snd \<circ> (summedBid bids)) a" 
  (is "?L=?R")
proof -
  let ?p = summedBid 
  let ?l = summedBidVector'
  have "?L = setsum snd ((?p bids)` a)" using assms by (rule lm59g)
  moreover have "... = ?R" using assms lm57c by blast
  ultimately show ?thesis by simp
qed

corollary lm25c: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "setsum (summedBidVector' bids N G) a = setsum ((setsum bids) \<circ> omega) a" 
  (is "?L=?R") 
proof -
  let ?inner1 = "snd \<circ> (summedBid bids)" 
  let ?inner2="(setsum bids) \<circ> omega"
  let ?M="setsum ?inner1 a"
  have "?L = ?M" using assms by (rule lm59h)
  moreover have "?inner1 = ?inner2" using lm25 assms by fastforce
  ultimately show "?L = ?R" using assms by metis
qed

corollary lm25d: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "setsum (summedBidVector' bids N G) a = setsum (setsum bids) (omega` a)"
proof -
  have "{} \<notin> Range a" using assms by (metis Universes.lm39b)
  then have "inj_on omega a" using lm32 by blast
  then have "setsum (setsum bids) (omega ` a) = setsum ((setsum bids) \<circ> omega) a" 
       by (rule setsum.reindex)
  moreover have "setsum (summedBidVector' bids N G) a = setsum ((setsum bids) \<circ> omega) a"
       using assms lm25c by (rule Extraction.exE_realizer)
  ultimately show ?thesis by presburger
qed

lemma lm67: 
  assumes "finite (snd pair)" 
  shows "finite (omega pair)" 
  using assms finite.emptyI finite.insertI finite_SigmaI finiteFinestpart  by (metis(no_types))

corollary lm67b: 
  assumes "\<forall>y\<in>(Range a). finite y" 
  shows "\<forall>y\<in>(omega ` a). finite y"
  using assms lm67 imageE finitePairSecondRange by fast

corollary lm67c: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "\<forall>x\<in>(omega ` a). finite x" 
  using assms lm67b lm41 by (metis(no_types))

corollary lm30b: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "is_non_overlapping (omega ` a)"
proof -
  have "runiq a" by (metis (no_types) assms image_iff lll81a)
  moreover have "{} \<notin> Range a" using assms by (metis Universes.lm39b)
  ultimately show ?thesis using lm30 by blast
qed

lemma lm68: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "setsum (setsum bids) (omega` a) = setsum bids (\<Union> (omega ` a))" 
  using assms setsumUnionDisjoint2 lm30b lm67c by (metis (lifting, mono_tags))

corollary lm69: 
  assumes "a \<in> possibleAllocationsRel N G" "finite G" 
  shows "setsum (summedBidVector' bids N G) a = setsum bids (pseudoAllocation a)" 
  (is "?L = ?R")
proof -
  have "?L = setsum (setsum bids) (omega `a)" using assms lm25d by blast
  moreover have "... = setsum bids (\<Union> (omega ` a))" using assms lm68 by blast
  ultimately show ?thesis unfolding pseudoAllocation_def by presburger
qed

lemma lm73: 
  "Domain (pseudoAllocation a) \<subseteq> Domain a"
  unfolding pseudoAllocation_def by fastforce

corollary lm73b: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "Domain (pseudoAllocation a) \<subseteq> N   &   Range (pseudoAllocation a) = finestpart G" 
  using assms lm73 lm47 lm55s is_partition_of_def subset_trans by (metis(no_types))

corollary lm73c: 
  assumes "a \<in> possibleAllocationsRel N G" 
  shows "pseudoAllocation a \<subseteq> N \<times> finestpart G"
proof -
  let ?p = pseudoAllocation 
  let ?aa = "?p a" 
  let ?d = Domain 
  let ?r = Range
  have "?d ?aa \<subseteq> N" using assms lm73b by (metis (lifting, mono_tags))
  moreover have "?r ?aa \<subseteq> finestpart G" using assms lm73b by (metis (lifting, mono_tags) equalityE)
  ultimately have "?d ?aa \<times> (?r ?aa) \<subseteq> N \<times> finestpart G" by auto
  then show "?aa \<subseteq> N \<times> finestpart G" by auto
qed








section{* From Pseudo-allocations to allocations  *}

(* pseudoAllocationInv inverts pseudoAllocation *)
abbreviation "pseudoAllocationInv pseudo == {(x, \<Union> (pseudo `` {x}))| x. x \<in> Domain pseudo}"
 
lemma lm75d: 
  assumes "runiq a" "{} \<notin> Range a" 
  shows "a = pseudoAllocationInv (pseudoAllocation a)"
proof -
  let ?p="{(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
  let ?a="{(x, \<Union> (?p `` {x}))| x. x \<in> Domain ?p}" 
  have "\<forall>x \<in> Domain a. a,,x \<noteq> {}" by (metis assms eval_runiq_in_Range)
  then have "\<forall>x \<in> Domain a. finestpart (a,,x) \<noteq> {}" by (metis notEmptyFinestpart) 
  then have "Domain a \<subseteq> Domain ?p" by force
  moreover have "Domain a \<supseteq> Domain ?p" by fast
  ultimately have 
  1: "Domain a = Domain ?p" by fast
  {
    fix z assume "z \<in> ?a" 
    then obtain x where 
    "x \<in> Domain ?p & z=(x , \<Union> (?p `` {x}))" by blast
    then have "x \<in> Domain a & z=(x , \<Union> (?p `` {x}))" by fast
    then moreover have "?p``{x} = finestpart (a,,x)" using assms by fastforce
    moreover have "\<Union> (finestpart (a,,x))= a,,x" by (metis finestPartUnion)
    ultimately have "z \<in> a" by (metis assms(1) eval_runiq_rel)
  }
  then have
  2: "?a \<subseteq> a" by fast
  {
    fix z assume 0: "z \<in> a" let ?x="fst z" let ?Y="a,,?x" let ?YY="finestpart ?Y"
    have "z \<in> a & ?x \<in> Domain a" using 0 by (metis fst_eq_Domain rev_image_eqI) 
    then have 
    3: "z \<in> a & ?x \<in> Domain ?p" using 1 by presburger  
    then have "?p `` {?x} = ?YY" by fastforce
    then have "\<Union> (?p `` {?x}) = ?Y" by (metis finestPartUnion)
    moreover have "z = (?x, ?Y)" using assms by (metis "0" functionOnFirstEqualsSecond
                                                           surjective_pairing)
    ultimately have "z \<in> ?a" using 3 by (metis (lifting, mono_tags) mem_Collect_eq)
  }
  then have "a = ?a" using 2 by blast
  moreover have "?p = pseudoAllocation a" using lm55v assms by (metis (lifting, mono_tags))
  ultimately show ?thesis by auto
qed

corollary lm75dd: 
  assumes "a \<in> runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}}))" 
  shows "(pseudoAllocationInv \<circ> pseudoAllocation) a = id a"
proof -
  have "runiq a" using runiqs_def assms by fast
  moreover have "{} \<notin> Range a" using assms by blast
  ultimately show ?thesis using lm75d by fastforce
qed

lemma lm75e: 
  "inj_on (pseudoAllocationInv \<circ> pseudoAllocation) (runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}})))" 
proof -
  let ?ne="Pow (UNIV \<times> (UNIV - {{}}))" 
  let ?X="runiqs \<inter> ?ne" 
  let ?f="pseudoAllocationInv \<circ> pseudoAllocation"
  have "\<forall>a1 \<in> ?X. \<forall> a2 \<in> ?X. ?f a1 = ?f a2 \<longrightarrow> id a1 = id a2" using lm75dd by blast 
  then have "\<forall>a1 \<in> ?X. \<forall> a2 \<in> ?X. ?f a1 = ?f a2 \<longrightarrow> a1 = a2" by auto
  thus ?thesis unfolding inj_on_def by blast
qed

corollary lm75g: 
  "inj_on pseudoAllocation (runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}})))" 
  using lm75e inj_on_imageI2 by blast

lemma lm76: 
  "injectionsUniverse \<subseteq> runiqs" 
  using runiqs_def Collect_conj_eq Int_lower1 by metis

lemma lm77: 
  "partitionValuedUniverse \<subseteq> Pow (UNIV \<times> (UNIV - {{}}))" 
  using assms is_non_overlapping_def by force

corollary lm75i: 
  "allocationsUniverse \<subseteq> runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}}))" 
  using lm76 lm77 by auto

corollary lm75h: 
  "inj_on pseudoAllocation allocationsUniverse" 
  using assms lm75g lm75i subset_inj_on by blast

corollary lm75j: 
  "inj_on pseudoAllocation (possibleAllocationsRel N G)" 
proof -
  have "possibleAllocationsRel N G \<subseteq> allocationsUniverse" by (metis (no_types) Universes.lm50)
  thus "inj_on pseudoAllocation (possibleAllocationsRel N G)" using lm75h subset_inj_on by blast
qed

lemma lm95: 
  assumes "card N > 0" "distinct G" 
  shows "winningAllocationsRel N (set G) bids \<subseteq> set (possibleAllocationsAlg N G)"
  using assms lm03 lm70b by (metis(no_types))

corollary lm96: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "winningAllocationsRel N (set G) bids \<inter> set (possibleAllocationsAlg N G) \<noteq> {}"
proof -
  let ?w = winningAllocationsRel 
  let ?a = possibleAllocationsAlg
  let ?G = "set G" 
  have "card N > 0" using assms by (metis card_gt_0_iff)
  then have "?w N ?G bids \<subseteq> set (?a N G)" using lm95 by (metis assms(3))
  then show ?thesis using assms lm91 by (metis List.finite_set le_iff_inf)
qed

(* -` is the reverse image *)
lemma lm97: 
  "X = (%x. x \<in> X) -`{True}" 
  by blast

corollary lm96b: 
  assumes  "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "(%x. x\<in>winningAllocationsRel N (set G) bids)-`{True} \<inter> 
         set (possibleAllocationsAlg N G) \<noteq> {}"
  using assms lm96 lm97 by metis

lemma lm84b: 
  assumes "P -` {True} \<inter> set l \<noteq> {}" 
  shows "takeAll P l \<noteq> []" 
  using assms nonEmptyListFiltered filterpositions2_def by (metis Nil_is_map_conv)

corollary lm84h: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "takeAll (%x. x \<in> winningAllocationsRel N (set G) bids) (possibleAllocationsAlg N G) \<noteq> []"
  using assms lm84b lm96b by metis

corollary nn05b: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "perm2 (takeAll (%x. x \<in> winningAllocationsRel N (set G) bids) 
                        (possibleAllocationsAlg N G)) 
               n \<noteq> []"
  using assms permutationNotEmpty lm84h by metis

(* The chosen allocation is in the set of possible winning allocations *)
corollary lm82: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "chosenAllocation' N G bids random \<in> winningAllocationsRel N (set G) bids"
proof -
  let ?w=winningAllocationsRel 
  let ?p=possibleAllocationsAlg 
  let ?G="set G"
  let ?X="?w N ?G bids" 
  let ?l="perm2 (takeAll (%x.(x\<in>?X)) (?p N G)) (nat_of_integer random)"
  have "set ?l \<subseteq> ?X" using takeAllPermutation by fast
  moreover have "?l \<noteq> []" using assms nn05b by blast
  ultimately show ?thesis by (metis (lifting, no_types) hd_in_set in_mono)
qed

(* The following lemma proves a property of maxbid', which in the following will be proved to maximize the revenue. a and aa are allocations. *)
lemma lm49b: 
  assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
  shows "real(setsum(maxbid' a N G)(pseudoAllocation a)) - 
            setsum(maxbid' a N G)(pseudoAllocation aa) = 
         real (card G) - 
            card (pseudoAllocation aa \<inter> (pseudoAllocation a))"
proof -
  let ?p = pseudoAllocation 
  let ?f = finestpart 
  let ?m = maxbid' 
  let ?B = "?m a N G" 
  have "?p aa \<subseteq> N \<times> ?f G" using assms lm73c by (metis (lifting, mono_tags)) 
  then have "?p aa \<subseteq> ?p a \<union> (N \<times> ?f G)" by auto 
  moreover have "finite (?p aa)" using assms lm48 lm54 by blast 
  ultimately have "real(setsum ?B (?p a)) - setsum ?B (?p aa) = 
                   real(card (?p a))-card(?p aa \<inter> (?p a))" 
    using differenceSetsumVsCardinalityReal by fast
  moreover have "... = real (card G) - card (?p aa \<inter> (?p a))" 
    using assms lm48 by (metis (lifting, mono_tags))
  ultimately show ?thesis by simp
qed

lemma lm66e: 
  "summedBidVectorRel bids N G = graph (N \<times> (Pow G-{{}})) (summedBidSecond bids)" 
  unfolding graph_def using lm66 by blast

lemma ll33b: 
  assumes "x\<in>X" 
  shows "toFunction (graph X f) x = f x" 
  using assms by (metis graphEqImage toFunction_def)

corollary ll33c: 
  assumes "pair \<in> N \<times> (Pow G-{{}})" 
  shows "summedBidVector' bids N G pair = summedBidSecond bids pair"
  using assms ll33b lm66e by (metis(mono_tags))

(* type conversion to real commutes *)
lemma lm031: 
  "summedBidSecond (real \<circ> ((bids:: _ => nat))) pair = real (summedBidSecond bids pair)" 
  by simp

lemma lm031b: 
  assumes "pair \<in> N \<times> (Pow G-{{}})" 
  shows  "summedBidVector' (real\<circ>(bids:: _ => nat)) N G pair = 
          real (summedBidVector' bids N G pair)" 
  using assms ll33c lm031 by (metis(no_types))

(* TPTP?*)
corollary lm031c: 
  assumes "X \<subseteq> N \<times> (Pow G - {{}})" 
  shows "\<forall>pair \<in> X. summedBidVector' (real \<circ> (bids::_=>nat)) N G pair =
         (real \<circ> (summedBidVector' bids N G)) pair"
proof -
  { fix esk48\<^sub>0 :: "'a \<times> 'b set"
    { assume "esk48\<^sub>0 \<in> N \<times> (Pow G - {{}})"
      hence "summedBidVector' (real \<circ> bids) N G esk48\<^sub>0 = real (summedBidVector' bids N G esk48\<^sub>0)" using lm031b by blast
      hence "esk48\<^sub>0 \<notin> X \<or> summedBidVector' (real \<circ> bids) N G esk48\<^sub>0 = (real \<circ> summedBidVector' bids N G) esk48\<^sub>0" by simp }
    hence "esk48\<^sub>0 \<notin> X \<or> summedBidVector' (real \<circ> bids) N G esk48\<^sub>0 = (real \<circ> summedBidVector' bids N G) esk48\<^sub>0" using assms by blast }
  thus "\<forall>pair\<in>X. summedBidVector' (real \<circ> bids) N G pair = (real \<circ> summedBidVector' bids N G) pair" by blast
qed

corollary lm031e: 
  assumes "aa \<subseteq> N \<times> (Pow G-{{}})" 
  shows "setsum ((summedBidVector' (real \<circ> (bids::_=>nat)) N G)) aa = 
         real (setsum ((summedBidVector' bids N G)) aa)" 
  (is "?L=?R")
proof -
  have "\<forall> pair \<in> aa. summedBidVector' (real \<circ> bids) N G pair = 
                     (real \<circ> (summedBidVector' bids N G)) pair"
  using assms by (rule lm031c)
  then have "?L = setsum (real\<circ>(summedBidVector' bids N G)) aa" using setsum.cong by force
  then show ?thesis by simp
qed

corollary lm031d: 
  assumes "aa \<in> possibleAllocationsRel N G" 
  shows "setsum ((summedBidVector' (real \<circ> (bids::_=>nat)) N G)) aa = 
         real (setsum ((summedBidVector' bids N G)) aa)" 
  using assms lm031e lm40c by (metis(lifting,mono_tags))

corollary lm70b: 
  assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
  shows "real (setsum (tiebids' a N G) a) - setsum (tiebids' a N G) aa = 
         real (card G) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" 
  (is "?L=?R")
proof -
  let ?l=summedBidVector' 
  let ?m=maxbid' 
  let ?s=setsum 
  let ?p=pseudoAllocation
  let ?bb="?m a N G" 
  let ?b="real \<circ> (?m a N G)"  
  have "real (?s ?bb (?p a)) - (?s ?bb (?p aa)) = ?R" using assms lm49b by blast 
  then have 
  1: "?R = real (?s ?bb (?p a)) - (?s ?bb (?p aa))" by simp
  have " ?s (?l ?b N G) aa = ?s ?b (?p aa)" using assms lm69 by blast moreover have 
  "... = ?s ?bb (?p aa)" by fastforce 
  moreover have "(?s (?l ?b N G) aa) = real (?s (?l ?bb N G) aa)" using assms(3) by (rule lm031d)
  ultimately have 
  2: "?R = real (?s ?bb (?p a)) - (?s (?l ?bb N G) aa)" by (metis 1)
  have "?s (?l ?b N G) a=(?s ?b (?p a))" using assms lm69 by blast
  moreover have "... = ?s ?bb (?p a)" by force
  moreover have "... = real (?s ?bb (?p a))" by fast
  moreover have "?s (?l ?b N G) a = real (?s (?l ?bb N G) a)" using assms(2) by (rule lm031d)
  ultimately have "?s (?l ?bb N G) a = real (?s ?bb (?p a))" by simp
  thus ?thesis using 2 by simp
qed

corollary lm70c: 
  assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
          "x = real (setsum (tiebids' a N G) a) - setsum (tiebids' a N G) aa" 
  shows "x <= card G & 
         x \<ge> 0 & 
        (x=0 \<longleftrightarrow> a = aa) & 
        (aa \<noteq> a \<longrightarrow> setsum (tiebids' a N G) aa < setsum (tiebids' a N G) a)"
proof -
  let ?p = pseudoAllocation 
  have "real (card G) >= real (card G) - card (?p aa \<inter> (?p a))" by force
  moreover have "real (setsum (tiebids' a N G) a) - setsum (tiebids' a N G) aa = 
                 real (card G) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))"
           using assms lm70b by blast 
  ultimately have
  1: "x=real(card G)-card(pseudoAllocation aa\<inter>(pseudoAllocation a))" using assms by force 
  then have
  2: "x \<le> real (card G)" using assms by linarith 
  have 
  3: "card (?p aa) = card G & card (?p a) = card G" using assms lm48 by blast 
  moreover have "finite (?p aa) & finite (?p a)" using assms lm54 by blast
  ultimately have "card (?p aa \<inter> ?p a) \<le> card G" using Int_lower2 card_mono by fastforce 
  then have 
  4: "x \<ge> 0" using assms lm70b 1 by linarith 
  have "card (?p aa \<inter> (?p a)) = card G \<longleftrightarrow> (?p aa = ?p a)" 
       using 3 lm56 4 assms by (metis (lifting, mono_tags))
  moreover have "?p aa = ?p a \<longrightarrow> a = aa" using assms lm75j inj_on_def 
       by (metis (lifting, mono_tags))
  ultimately have "card (?p aa \<inter> (?p a)) = card G \<longleftrightarrow> (a=aa)" by blast
  moreover have "x = real (card G) - card (?p aa \<inter> (?p a))" using assms lm70b by blast
  ultimately have 
  5: "x = 0 \<longleftrightarrow> (a=aa)" by linarith 
  then have 
  "aa \<noteq> a \<longrightarrow> setsum (tiebids' a N G) aa < real (setsum (tiebids' a N G) a)" 
        using 1 4 assms by auto
  thus ?thesis using 2 4 5 by force
qed 

(* If for an arbitrary allocation a we compute tiebids for it then the corresponding revenue is strictly maximal. *)
corollary lm70d: 
  assumes "finite G" "a \<in> possibleAllocationsRel N G" 
          "aa \<in> possibleAllocationsRel N G" "aa \<noteq> a" 
  shows "setsum (tiebids' a N G) aa < setsum (tiebids' a N G) a" 
  using assms lm70c by blast

lemma lm81: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}"
          "aa \<in> (possibleAllocationsRel N (set G))-{chosenAllocation' N G bids random}" 
  shows "setsum (resolvingBid' N G bids random) aa < 
         setsum (resolvingBid' N G bids random) (chosenAllocation' N G bids random)" 
proof -
  let ?a="chosenAllocation' N G bids random" 
  let ?p=possibleAllocationsRel 
  let ?G="set G"
  have "?a \<in> winningAllocationsRel N (set G) bids" using assms lm82 by blast
  moreover have "winningAllocationsRel N (set G) bids \<subseteq> ?p N ?G" using assms lm03 by metis
  ultimately have "?a \<in> ?p N ?G" using lm82 assms lm03 set_rev_mp by blast
  then show ?thesis using assms lm70d by blast 
qed

(* putting together the two rounds in the auction, first using the bids, then the random values. *)
abbreviation "terminatingAuctionRel N G bids random == 
              argmax (setsum (resolvingBid' N G bids random)) 
                     (argmax (setsum bids) (possibleAllocationsRel N (set G)))"

text{* Termination theorem: it assures that the number of winning allocations is exactly one *}
theorem winningAllocationUniqueness: 
  assumes "N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N"
  shows "terminatingAuctionRel N G (bids) random = {chosenAllocation' N G bids random}"
proof -
  let ?p = possibleAllocationsRel 
  let ?G = "set G" 
  let ?X = "argmax (setsum bids) (?p N ?G)"
  let ?a = "chosenAllocation' N G bids random" 
  let ?b = "resolvingBid' N G bids random"
  let ?f = "setsum ?b" 
  let ?t=terminatingAuctionRel 
  have "\<forall>aa \<in> (possibleAllocationsRel N ?G)-{?a}. ?f aa < ?f ?a" 
    using assms lm81 by blast 
  then have "\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a" using assms lm81 by auto
  moreover have "finite N" using assms by simp 
  then have "finite (?p N ?G)" using assms lm59 by (metis List.finite_set)
  then have "finite ?X" using assms by (metis finite_subset lm03)
  moreover have "?a \<in> ?X" using lm82 assms by blast
  ultimately have "finite ?X & ?a \<in> ?X & (\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a)" by force
  moreover have "(finite ?X & ?a \<in> ?X & (\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a)) \<longrightarrow> argmax ?f ?X = {?a}"
    by (rule argmaxProperty)
  ultimately have "{?a} = argmax ?f ?X" using lm80 by presburger
  moreover have "... = ?t N G bids random" by simp
  ultimately show ?thesis by simp
qed

text {* The computable variant of Else is defined next as Elsee. *}
definition "toFunctionWithFallbackAlg R fallback == 
            (% x. if (x \<in> Domain R) then (R,,x) else fallback)"
notation toFunctionWithFallbackAlg (infix "Elsee" 75) 

end

