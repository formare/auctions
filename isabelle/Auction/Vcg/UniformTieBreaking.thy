(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Author: Marco B. Caminati http://caminati.co.nr

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

section {* Termination theorem for the uniform tie-breaking scheme @{term resolvingBid'} *}

corollary lm03: "winningAllocationsRel N G b \<subseteq> possibleAllocationsRel N G" 
using lm02 mem_Collect_eq subsetI by auto

lemma lm35b: assumes "a \<in> allocationsUniverse" "c \<subseteq> a" shows "c \<in> allocationsUniverse"  
proof - have "c=a-(a-c)" using assms(2) by blast thus ?thesis using assms(1) lm35 by (metis (no_types)) qed
lemma lm35c: assumes "a \<in> allocationsUniverse" shows "a outside X \<in> allocationsUniverse"
using assms lm35 Outside_def by (metis (no_types))

corollary lm38d: "{x}\<times>({X}-{{}}) \<in> allocationsUniverse" using lm38 nn43 by metis
corollary lm38b: "{(x,{y})} \<in> allocationsUniverse" using lm38 lm44 insert_not_empty 
proof -
  have "(x, {y}) \<noteq> (x, {})" by blast
  thus "{(x, {y})} \<in> allocationsUniverse" by (metis (no_types) insert_Diff_if insert_iff lm38 lm44)
qed
corollary lm38c: "allocationsUniverse \<noteq> {}" using lm38b by fast
corollary nn39: "{} \<in> allocationsUniverse" using lm35b lm38b by (metis (lifting, mono_tags) empty_subsetI)
lemma mm87: assumes "G \<noteq> {}" shows "{G} \<in> all_partitions G" using all_partitions_def is_partition_of_def 
is_partition_def assms by force
lemma mm88: assumes "n \<in> N" shows "{(G,n)} \<in> totalRels {G} N" using assms by force
lemma mm89: assumes "n\<in>N" shows "{(G,n)} \<in> injections {G} N" 
using assms possible_allocations_rel_def injections_def mm87 all_partitions_def 
is_partition_def is_partition_of_def lm26 mm88 lm37 lm24 by fastforce
corollary mm90: assumes " G\<noteq>{}" "n\<in>N" shows "{(G,n)} \<in> possible_allocations_rel G N"
proof -
  have "{(G,n)} \<in> injections {G} N" using assms mm89 by fast
  moreover have "{G} \<in> all_partitions G" using assms mm87 by metis
  ultimately show ?thesis using possible_allocations_rel_def by auto
qed
corollary mm90b: assumes "N \<noteq> {}" "G\<noteq>{}" shows "possibleAllocationsRel N G \<noteq> {}"
using assms mm90 by (metis (hide_lams, no_types) equals0I image_insert insert_absorb insert_not_empty)
corollary mm91: assumes "N \<noteq> {}" "finite N" "G \<noteq> {}" "finite G" shows 
"winningAllocationsRel N G bids \<noteq> {} & finite (winningAllocationsRel N G bids)" 
using assms mm90b lm59 argmax_non_empty_iff by (metis lm03 rev_finite_subset)

lemma mm52: "possibleAllocationsRel N {} \<subseteq> {{}}" using emptyset_part_emptyset3 mm51 
lm28b mem_Collect_eq subsetI vimage_def by metis

lemma mm42: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "finite (Range a)" 
using assms lm55 by (metis lm28)

corollary mm44: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "finite a"
using assms mm42 mm43 finite_converse 
by (metis (erased, hide_lams) Range_converse imageE lll81)

lemma assumes "a \<in> possibleAllocationsRel N G" shows "\<Union> Range a = G" using assms 
by (metis is_partition_of_def lm47)

lemma mm41: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows
"\<forall> y \<in> Range a. finite y" using assms is_partition_of_def lm47 by (metis Union_upper rev_finite_subset)

corollary mm33c: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"card G = setsum card (Range a)" using assms mm33b mm42 lm47 by (metis is_partition_of_def)
























lemma mm66: "LinearCompletion bids N G = 
{(pair,setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))|pair. pair \<in> N \<times> (Pow G-{{}})}" by blast
corollary mm65b: 
"{(pair,setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))|pair. pair \<in> N \<times> (Pow G-{{}})} || a = 
{(pair,setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))|pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
by (metis mm65)
corollary mm66b: "(LinearCompletion bids N G) || a = 
{(pair,setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))|pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
(is "?L=?R") using mm65b mm66 
proof -
let ?l=LinearCompletion
let ?M="{(pair,setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))|pair. pair \<in> N \<times> (Pow G-{{}})}"
have "?l bids N G = ?M" by (rule mm66)
then have "?L = (?M || a)" by presburger
moreover have "... = ?R" by (rule mm65b)
ultimately show ?thesis by presburger
qed
lemma mm66c: "(partialCompletionOf bids) ` ((N \<times> (Pow G - {{}})) \<inter> a) = 
{(pair,setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))|pair. pair \<in> (N \<times> (Pow G-{{}})) \<inter> a}"
by blast
corollary mm66d: "(LinearCompletion bids N G) || a = (partialCompletionOf bids) ` ((N \<times> (Pow G - {{}})) \<inter> a)"
(is "?L=?R")
using mm66c mm66b 
proof -
let ?l=LinearCompletion let ?p=partialCompletionOf let ?M="{
(pair,setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))|pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
have "?L = ?M" by (rule mm66b)
moreover have "... = ?R" using mm66c by blast
ultimately show ?thesis by presburger
qed
lemma mm57: "inj_on (partialCompletionOf bids) UNIV" using assms by (metis (lifting) fst_conv inj_on_inverseI)
corollary mm57b: "inj_on (partialCompletionOf bids) X" using fst_conv inj_on_inverseI by (metis (lifting))
lemma mm58: "setsum snd (LinearCompletion bids N G) = 
setsum (snd \<circ> (partialCompletionOf bids)) (N \<times> (Pow G - {{}}))" using assms 
mm57b setsum.reindex by blast 
corollary mm25: "snd (partialCompletionOf bids pair)=setsum bids (omega pair)" using mm24 by force
corollary mm25b: "snd \<circ> partialCompletionOf bids = (setsum bids) \<circ> omega" using mm25 by fastforce

(* lemma assumes "x \<in> X \<inter> Domain f" "runiq f" shows "toFunction (f||X) x = toFunction f x" using assms eval_rel_def restrict_def
toFunction_def runiq_def *)

lemma mm27: assumes "finite  (finestpart (snd pair))" shows 
"card (omega pair) = card (finestpart (snd pair))" using assms by force

corollary assumes "finite (snd pair)" shows "card (omega pair) = card (snd pair)" 
using assms mm26 card_cartesian_product_singleton by metis

lemma mm30: assumes "{} \<notin> Range f" "runiq f" shows "is_partition (omega ` f)"
(* MC: generalize and clean *)
proof -
let ?X="omega ` f" let ?p=finestpart
  { fix y1 y2; assume "y1 \<in> ?X & y2 \<in> ?X"
    then obtain pair1 pair2 where 
    0: "y1 = omega pair1 & y2 = omega pair2 & pair1 \<in> f & pair2 \<in> f" by blast
    then moreover have "snd pair1 \<noteq> {} & snd pair1 \<noteq> {}" using assms
by (metis rev_image_eqI snd_eq_Range)
    ultimately moreover have "fst pair1 = fst pair2 \<longleftrightarrow> pair1 = pair2" using assms
    runiq_basic surjective_pairing by metis
    ultimately moreover have "y1 \<inter> y2 \<noteq> {} \<longrightarrow> y1 = y2" using assms 0 by fast
    ultimately have "y1 = y2 \<longleftrightarrow> y1 \<inter> y2 \<noteq> {}" using assms mm29 
    by (metis Int_absorb Times_empty insert_not_empty)
    }
  thus ?thesis using is_partition_def by (metis (lifting, no_types) inf_commute inf_sup_aci(1))
qed

lemma mm32: assumes "{} \<notin> Range X" shows "inj_on omega X"
proof -
let ?p=finestpart
{
  fix pair1 pair2 assume "pair1 \<in> X & pair2 \<in> X" then have 
  0: "snd pair1 \<noteq> {} & snd pair2 \<noteq> {}" using assms by (metis Range.intros surjective_pairing)
  assume "omega pair1 = omega pair2" then moreover have "?p (snd pair1) = ?p (snd pair2)" by blast
  then moreover have "snd pair1 = snd pair2" by (metis ll64 mm31)
  ultimately moreover have "{fst pair1} = {fst pair2}" using 0 mm29 by (metis fst_image_times)
  ultimately have "pair1 = pair2" by (metis prod_eqI singleton_inject)
}
thus ?thesis by (metis (lifting, no_types) inj_onI)
qed

lemma mm36: assumes "{} \<notin> Range a" 
"finite (omega ` a)" "\<forall>X \<in> omega ` a. finite X" "is_partition (omega ` a)"
shows "card (pseudoAllocation a) = setsum (card \<circ> omega) a" (is "?L = ?R")
using assms mm33 UniformTieBreaking.mm32 setsum.reindex 
proof -
have "?L = setsum card (omega ` a)" using assms(2,3,4) by (rule mm33)
moreover have "... = ?R" using assms(1) mm32 setsum.reindex by blast
ultimately show ?thesis by presburger
qed

lemma mm35: "card (omega pair)= card (snd pair)" 
using mm26 card_cartesian_product_singleton by metis

corollary mm35b: "card \<circ> omega = card \<circ> snd" using mm35 by fastforce

corollary mm37: assumes "{} \<notin> Range a" "\<forall> pair \<in> a. finite (snd pair)" "finite a" "runiq a" 
shows "card (pseudoAllocation a) = setsum (card \<circ> snd) a"
proof -
let ?P=pseudoAllocation let ?c=card
have "\<forall> pair \<in> a. finite (omega pair)" using mm40 assms by blast moreover
have "is_partition (omega ` a)" using assms mm30 by force ultimately
have "?c (?P a) = setsum (?c \<circ> omega) a" using assms mm36 by force
moreover have "... = setsum (?c \<circ> snd) a" using mm35b by metis
ultimately show ?thesis by presburger
qed

corollary mm46: assumes 
"runiq (a^-1)" "runiq a" "finite a" "{} \<notin> Range a" "\<forall> pair \<in> a. finite (snd pair)" shows 
"card (pseudoAllocation a) = setsum card (Range a)" using assms mm39 mm37 by force

corollary mm48: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"card (pseudoAllocation a) = card G"
proof -
  have "{} \<notin> Range a" using assms mm45b by blast
  moreover have "\<forall> pair \<in> a. finite (snd pair)" using assms mm41 mm47 by metis
  moreover have "finite a" using assms mm44 by blast
  moreover have "runiq a" using assms by (metis (lifting) Int_lower1 in_mono lm19 mem_Collect_eq)
  moreover have "runiq (a^-1)" using assms by (metis (mono_tags) injections_def lm28b mem_Collect_eq)
  ultimately have "card (pseudoAllocation a) = setsum card (Range a)" using mm46 by fast
  moreover have "... = card G" using assms mm33c by metis
  ultimately show ?thesis by presburger
qed

corollary mm49: assumes 
"pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" "finite (pseudoAllocation aa)"
shows "setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation a) - 
(setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation aa)) = 
card (pseudoAllocation a) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" using mm28 assms
by blast

corollary mm49c: assumes 
"pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" "finite (pseudoAllocation aa)"
shows "int (setsum (maxbid' a N G) (pseudoAllocation a)) - 
int (setsum (maxbid' a N G) (pseudoAllocation aa)) = 
int (card (pseudoAllocation a)) - int (card (pseudoAllocation aa \<inter> (pseudoAllocation a)))" using mm28b assms
by blast

lemma mm50: "pseudoAllocation {} = {}" by simp

corollary mm53b: assumes "a \<in> possibleAllocationsRel N {}" shows "(pseudoAllocation a)={}"
using assms mm52 by blast

corollary mm53: assumes "a \<in> possibleAllocationsRel N G" "finite G" "G \<noteq> {}"
shows "finite (pseudoAllocation a)" 
proof -
  have "card (pseudoAllocation a) = card G" using assms(1,2) mm48 by blast
  thus "finite (pseudoAllocation a)" using assms(2,3) by fastforce
qed

corollary mm54: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"finite (pseudoAllocation a)" using assms finite.emptyI mm53 mm53b by (metis (no_types))

lemma mm56: assumes "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G" "finite G" shows 
"(card (pseudoAllocation aa \<inter> (pseudoAllocation a)) = card (pseudoAllocation a)) = 
(pseudoAllocation a = pseudoAllocation aa)" using assms mm48 mm23b 
proof -
let ?P=pseudoAllocation let ?c=card let ?A="?P a" let ?AA="?P aa"
have "?c ?A=?c G & ?c ?AA=?c G" using assms mm48 by (metis (lifting, mono_tags))
moreover have "finite ?A & finite ?AA" using assms mm54 by blast
ultimately show ?thesis using assms mm23b by (metis(no_types,lifting))
qed

lemma mm55: "omega pair = {fst pair} \<times> {{y}| y. y \<in> snd pair}" using finestpart_def ll64 by auto

lemma mm55c: "omega pair = {(fst pair, {y})| y. y \<in>  snd pair}" using mm55 mm55b by metis

lemma mm55d: "pseudoAllocation a = \<Union> {{(fst pair, {y})| y. y \<in> snd pair}| pair. pair \<in> a}"
using mm55c by blast
lemma mm55e: "\<Union> {{(fst pair, {y})| y. y \<in> snd pair}| pair. pair \<in> a}=
{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" by blast

corollary mm55k: "pseudoAllocation a = {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a}" 
using mm55j by blast

lemma mm55u: assumes "runiq a" shows 
"{(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a} = {(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
(is "?L=?R") using assms Domain.DomainI fst_conv mm60 runiq_wrt_ex1 surjective_pairing
by (metis(hide_lams,no_types))

corollary mm55v: assumes "runiq a" shows "pseudoAllocation a = {(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
using assms mm55u mm55k by fastforce

corollary mm55t: "Range (pseudoAllocation a) = \<Union> (finestpart ` (Range a))" 
using mm55k mm55l mm55m by fastforce

corollary mm55s: "Range (pseudoAllocation a) = finestpart (\<Union> Range a)" using mm55r mm55t by metis 


lemma mm55f: "pseudoAllocation a = {(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" using mm55d 
mm55e by (metis (full_types))
lemma mm55g: "{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}=
{(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a}" by auto

lemma mm55i: "pseudoAllocation a = {(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a}" (is "?L=?R")
proof -
have "?L={(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" by (rule mm55f)
moreover have "... = ?R" by (rule mm55g) ultimately show ?thesis by presburger
qed

lemma mm62: "runiq (LinearCompletion bids N G)" using assms by (metis graph_def image_Collect_mem ll37)
corollary mm62b: "runiq (LinearCompletion bids N G || a)"
unfolding restrict_def using mm62 subrel_runiq Int_commute by blast
lemma mm64: "N \<times> (Pow G - {{}}) = Domain (LinearCompletion bids N G)" by blast

corollary mm63d: assumes "a \<in> possibleAllocationsRel N G" shows "a \<subseteq> Domain (LinearCompletion bids N G)"
proof -
let ?p=possibleAllocationsRel let ?L=LinearCompletion
have "a \<subseteq> N \<times> (Pow G - {{}})" using assms mm63c by metis
moreover have "N \<times> (Pow G - {{}})=Domain (?L bids N G)" using mm64 by blast
ultimately show ?thesis by blast
qed

corollary mm59d: "setsum (linearCompletion' bids N G) (a \<inter> (Domain (LinearCompletion bids N G))) = 
setsum snd ((LinearCompletion bids N G) || a)" using assms mm59c mm62b by fast

corollary mm59e: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion' bids N G) a = setsum snd ((LinearCompletion bids N G) || a)" 
proof -
let ?l=linearCompletion' let ?L=LinearCompletion
have "a \<subseteq> Domain (?L bids N G)" using assms by (rule mm63d) then
have "a = a \<inter> Domain (?L bids N G)" by blast then
have "setsum (?l bids N G) a = setsum (?l bids N G) (a \<inter> Domain (?L bids N G))" by presburger
thus ?thesis using mm59d by auto
qed

corollary mm59f: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion' bids N G) a = setsum snd ((partialCompletionOf bids) ` ((N \<times> (Pow G - {{}})) \<inter> a))"
(is "?X=?R")
proof -
let ?p=partialCompletionOf let ?L=LinearCompletion let ?l=linearCompletion'
let ?A="N \<times> (Pow G - {{}})" let ?inner2="(?p bids)`(?A \<inter> a)" let ?inner1="(?L bids N G)||a"
have "?R = setsum snd ?inner1" using assms mm66d by (metis (no_types))
moreover have "setsum (?l bids N G) a = setsum snd ?inner1" using assms by (rule mm59e)
ultimately show ?thesis by presburger
qed
corollary mm59g: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion' bids N G) a = setsum snd ((partialCompletionOf bids) ` a)" (is "?L=?R")
using assms mm59f mm63c 
proof -
let ?p=partialCompletionOf let ?l=linearCompletion'
have "?L = setsum snd ((?p bids)`((N \<times> (Pow G - {{}}))\<inter> a))" using assms by (rule mm59f)
moreover have "... = ?R" using assms mm63c Int_absorb1 by (metis (no_types))
ultimately show ?thesis by presburger
qed
corollary mm57c: "setsum snd ((partialCompletionOf bids) ` a) = setsum (snd \<circ> (partialCompletionOf bids)) a"
using assms setsum.reindex mm57b by blast
corollary mm59h: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion' bids N G) a = setsum (snd \<circ> (partialCompletionOf bids)) a" (is "?L=?R")
using assms mm59g mm57c 
proof -
let ?p=partialCompletionOf let ?l=linearCompletion'
have "?L = setsum snd ((?p bids)` a)" using assms by (rule mm59g)
moreover have "... = ?R" using assms mm57c by blast
ultimately show ?thesis by presburger
qed
corollary mm25c: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion' bids N G) a = setsum ((setsum bids) \<circ> omega) a" (is "?L=?R") 
using assms mm59h mm25 
proof -
let ?inner1="snd \<circ> (partialCompletionOf bids)" let ?inner2="(setsum bids) \<circ> omega"
let ?M="setsum ?inner1 a"
have "?L = ?M" using assms by (rule mm59h)
moreover have "?inner1 = ?inner2" using mm25 assms by fastforce
ultimately show "?L = ?R" using assms by metis
qed

corollary mm25d: assumes "a \<in> possibleAllocationsRel N G" shows
"setsum (linearCompletion' bids N G) a = setsum (setsum bids) (omega` a)"
using assms mm25c setsum.reindex mm32 
proof -
have "{} \<notin> Range a" using assms by (metis mm45b)
then have "inj_on omega a" using mm32 by blast
then have "setsum (setsum bids) (omega ` a) = setsum ((setsum bids) \<circ> omega) a" 
by (rule setsum.reindex)
moreover have "setsum (linearCompletion' bids N G) a = setsum ((setsum bids) \<circ> omega) a"
using assms mm25c by (rule Extraction.exE_realizer)
ultimately show ?thesis by presburger
qed

lemma mm67: assumes "finite (snd pair)" shows "finite (omega pair)" using assms 
by (metis finite.emptyI finite.insertI finite_SigmaI mm40)
corollary mm67b: assumes "\<forall>y\<in>(Range a). finite y" shows "\<forall>y\<in>(omega ` a). finite y"
using assms mm67 imageE mm47 by fast
lemma assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "\<forall>y \<in> (Range a). finite y"
using assms by (metis mm41)

corollary mm67c: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "\<forall>x\<in>(omega ` a). finite x" 
using assms mm67b mm41 by (metis(no_types))

corollary mm30b: assumes "a \<in> possibleAllocationsRel N G" shows "is_partition (omega ` a)"
using assms mm30 mm45b image_iff lll81a 
proof -
  have "runiq a" by (metis (no_types) assms image_iff lll81a)
  moreover have "{} \<notin> Range a" using assms mm45b by blast
  ultimately show ?thesis using mm30 by blast
qed

lemma mm68: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"setsum (setsum bids) (omega` a) = setsum bids (\<Union> (omega ` a)) " 
using assms setsum_Union_disjoint_2 mm30b mm67c by (metis (lifting, mono_tags))

corollary mm69: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"setsum (linearCompletion' bids N G) a = setsum bids (pseudoAllocation a)" (is "?L = ?R")
using assms mm25d mm68 
proof -
have "?L = setsum (setsum bids) (omega `a)" using assms mm25d by blast
moreover have "... = setsum bids (\<Union> (omega ` a))" using assms mm68 by blast
ultimately show ?thesis by presburger
qed

lemma mm73: "Domain (pseudoAllocation a) \<subseteq> Domain a" by auto 
corollary assumes "a \<in> possibleAllocationsRel N G" shows "\<Union> Range a = G" using assms lm47 
is_partition_of_def by metis
corollary mm72: assumes "a \<in> possibleAllocationsRel N G" shows "Range (pseudoAllocation a) = finestpart G" 
using assms mm55s lm47 is_partition_of_def by metis
corollary mm73b: assumes "a \<in> possibleAllocationsRel N G" shows "Domain (pseudoAllocation a) \<subseteq> N & 
Range (pseudoAllocation a) = finestpart G" 
using assms mm73 lm47 mm55s is_partition_of_def subset_trans by (metis(no_types))
corollary mm73c: assumes "a \<in> possibleAllocationsRel N G" 
shows "pseudoAllocation a \<subseteq> N \<times> finestpart G" using assms mm73b 
proof -
let ?p=pseudoAllocation let ?aa="?p a" let ?d=Domain let ?r=Range
have "?d ?aa \<subseteq> N" using assms mm73b by (metis (lifting, mono_tags))
moreover have "?r ?aa \<subseteq> finestpart G" using assms mm73b by (metis (lifting, mono_tags) equalityE)
ultimately have "?d ?aa \<times> (?r ?aa) \<subseteq> N \<times> finestpart G" by auto
then show "?aa \<subseteq> N \<times> finestpart G" by auto
qed


































abbreviation "mbc pseudo == {(x, \<Union> (pseudo `` {x}))| x. x \<in> Domain pseudo}"
 
corollary assumes "{} \<notin> Range X" shows "inj_on (image omega) (Pow X)" using assms mm74 mm32 by blast

lemma "pseudoAllocation = Union \<circ> (image omega)" by force
lemma mm75d: assumes "runiq a" "{} \<notin> Range a" shows 
"a = mbc (pseudoAllocation a)"
proof -
let ?p="{(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
let ?a="{(x, \<Union> (?p `` {x}))| x. x \<in> Domain ?p}" 
have "\<forall>x \<in> Domain a. a,,x \<noteq> {}" by (metis assms ll14)
then have "\<forall>x \<in> Domain a. finestpart (a,,x) \<noteq> {}" by (metis mm29) 
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
  moreover have "\<Union> (finestpart (a,,x))= a,,x" by (metis mm75)
  ultimately have "z \<in> a" by (metis assms(1) eval_runiq_rel)
  }
then have
3: "?a \<subseteq> a" by fast
{
  fix z assume 0: "z \<in> a" let ?x="fst z" let ?Y="a,,?x" let ?YY="finestpart ?Y"
  have "z \<in> a & ?x \<in> Domain a" using 0 by (metis fst_eq_Domain rev_image_eqI) then
  have 
  2:"z \<in> a & ?x \<in> Domain ?p" using 1 by presburger  then
  have "?p `` {?x} = ?YY" by fastforce
  then have "\<Union> (?p `` {?x}) = ?Y" by (metis mm75)
  moreover have "z = (?x, ?Y)" using assms by (metis "0" mm60 surjective_pairing)
  ultimately have "z \<in> ?a" using 2 by (metis (lifting, mono_tags) mem_Collect_eq)
  }
then have "a = ?a" using 3 by blast
moreover have "?p = pseudoAllocation a" using mm55v assms by (metis (lifting, mono_tags))
ultimately show ?thesis by auto
qed
corollary mm75dd: assumes "a \<in> runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}}))" shows
"(mbc \<circ> pseudoAllocation) a = id a" using assms mm75d 
proof -
have "runiq a" using runiqs_def assms by fast
moreover have "{} \<notin> Range a" using assms by blast
ultimately show ?thesis using mm75d by fastforce
qed
lemma mm75e: "inj_on (mbc \<circ> pseudoAllocation) (runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}})))" 
using assms mm75dd inj_on_def inj_on_id 
proof -
let ?ne="Pow (UNIV \<times> (UNIV - {{}}))" let ?X="runiqs \<inter> ?ne" let ?f="mbc \<circ> pseudoAllocation"
have "\<forall>a1 \<in> ?X. \<forall> a2 \<in> ?X. ?f a1 = ?f a2 \<longrightarrow> id a1 = id a2" using mm75dd by blast then 
have "\<forall>a1 \<in> ?X. \<forall> a2 \<in> ?X. ?f a1 = ?f a2 \<longrightarrow> a1 = a2" by auto
thus ?thesis unfolding inj_on_def by blast
qed

corollary mm75g: "inj_on pseudoAllocation (runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}})))" 
using mm75e inj_on_imageI2 by blast
lemma mm76: "injectionsUniverse \<subseteq> runiqs" using runiqs_def Collect_conj_eq Int_lower1 by metis
lemma mm77: "partitionValuedUniverse \<subseteq> Pow (UNIV \<times> (UNIV - {{}}))" using assms is_partition_def by force
corollary mm75i: "allocationsUniverse \<subseteq> runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}}))" using mm76 mm77 by auto
corollary mm75h: "inj_on pseudoAllocation allocationsUniverse" using assms mm75g mm75i subset_inj_on by blast
corollary mm75j: "inj_on pseudoAllocation (possibleAllocationsRel N G)" 
proof -
  have "possibleAllocationsRel N G \<subseteq> allocationsUniverse" by (metis (no_types) lm50)
  thus "inj_on pseudoAllocation (possibleAllocationsRel N G)" using mm75h subset_inj_on by blast
qed








































fun prova where "prova f X 0 = X" | "prova f X (Suc n) = f n (prova f X n)"

fun prova2 where "prova2 f 0 = UNIV" |"prova2 f (Suc n) = f n (prova2 f n)"

fun geniter where "geniter f 0 = f 0" | "geniter f (Suc n)=(f (Suc n)) o (geniter f n)"

abbreviation "pseudodecreasing X Y == card X - 1 \<le> card Y - 2"
(* We'll use this to model the behaviour {1,2,3} -> {1,2} -> {1} -> {1} -> {1} ... *)
notation pseudodecreasing (infix "<~" 75)

abbreviation "subList l xl == map (nth l) (takeAll (%x. x \<le> size l) xl)"
abbreviation "insertRightOf2 x l n == (subList l (map nat [0..n])) @ [x] @ 
(subList l (map nat [n+1..size l - 1]))"
abbreviation "insertRightOf3 x l n == insertRightOf2 x l (Min {n, size l - 1})"
definition "insertRightOf x l n = sublist l {0..<1+n} @ [x] @ sublist l {n+1..< 1+size l}"
lemma "set (insertRightOf x l n) = set (sublist l {0..<1+n}) \<union> (set [x]) \<union> 
set (sublist l {n+1..<1+size l})" using insertRightOf_def 
by (metis append_assoc set_append)
lemma "set l1 \<union> set l2 = set (l1 @ l2)" by simp

fun permOld::"'a list => (nat \<times> ('a list)) set" where 
"permOld [] = {}" | "permOld (x#l) = 
graph {fact (size l) ..< 1+fact (1 + (size l))}
(%n::nat. insertRightOf x (permOld l,,(n div size l)) (n mod (size l)))
+* (permOld l)"

fun permL where (* associate to every n=1...(size l)! a unique permutation of l, 
parsing all and only the possible permutations (assuming distinct l)*)
"permL [] = (%n. [])"|
"permL (x#l) = (%n. 
if (fact (size l) < n & n <= fact (1 + (size l)))
then
(insertRightOf3 x (permL l (n div size l)) (n mod (size l)))
else
(x # (permL l n))
)"

lemma mm94: "possibleAllocationsAlg2 N G = set (possibleAllocationsAlg3 N G)" by auto
lemma mm95: assumes "card N > 0" "distinct G" shows 
"winningAllocationsRel N (set G) bids \<subseteq> set (possibleAllocationsAlg3 N G)"
using assms mm94 lm03 lm70b by (metis(no_types))
corollary mm96: assumes 
"N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows
"winningAllocationsRel N (set G) bids \<inter> set (possibleAllocationsAlg3 N G) \<noteq> {}"
using assms mm91 mm95 
proof -
let ?w=winningAllocationsRel let ?a=possibleAllocationsAlg3
let ?G="set G" have "card N > 0" using assms by (metis card_gt_0_iff)
then have "?w N ?G bids \<subseteq> set (?a N G)" using mm95 by (metis assms(3))
then show ?thesis using assms mm91 by (metis List.finite_set le_iff_inf)
qed
lemma mm97: "X = (%x. x \<in> X) -`{True}" by blast
corollary mm96b: assumes 
"N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows
"(%x. x\<in>winningAllocationsRel N (set G) bids)-`{True} \<inter> set (possibleAllocationsAlg3 N G) \<noteq> {}"
using assms mm96 mm97 by metis
lemma mm84b: assumes "P -` {True} \<inter> set l \<noteq> {}" shows "takeAll P l \<noteq> []" using assms
mm84g filterpositions2_def by (metis Nil_is_map_conv)
corollary mm84h: assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows 
"takeAll (%x. x \<in> winningAllocationsRel N (set G) bids) (possibleAllocationsAlg3 N G) \<noteq> []"
using assms mm84b mm96b by metis

corollary nn05b: assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows 
"perm2 (takeAll (%x. x \<in> winningAllocationsRel N (set G) bids) (possibleAllocationsAlg3 N G)) n \<noteq> []"
using assms mm83 mm84h by metis
corollary mm82: assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows 
"chosenAllocation' N G bids random \<in> winningAllocationsRel N (set G) bids"
using assms nn05a nn05b hd_in_set in_mono Int_def Int_lower1 all_not_in_conv image_set nn04 nn06c set_empty subsetI subset_trans
proof -
let ?w=winningAllocationsRel let ?p=possibleAllocationsAlg3 let ?G="set G"
let ?X="?w N ?G bids" let ?l="perm2 (takeAll (%x.(x\<in>?X)) (?p N G)) random"
have "set ?l \<subseteq> ?X" using nn05a by fast
moreover have "?l \<noteq> []" using assms nn05b by blast
ultimately show ?thesis by (metis (lifting, no_types) hd_in_set in_mono)
qed

lemma mm49b: assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
shows "real(setsum(maxbid' a N G)(pseudoAllocation a)) - setsum(maxbid' a N G)(pseudoAllocation aa) 
= real (card G) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))"
proof -
let ?p=pseudoAllocation let ?f=finestpart let ?m=maxbid' let ?B="?m a N G" have 
2: "?p aa \<subseteq> N \<times> ?f G" using assms mm73c by (metis (lifting, mono_tags)) then have 
0: "?p aa \<subseteq> ?p a \<union> (N \<times> ?f G)" by auto moreover have 
1: "finite (?p aa)" using assms mm48 mm54 by blast ultimately have 
"real(setsum ?B (?p a))-setsum ?B (?p aa) = real(card (?p a))-card(?p aa \<inter> (?p a))" 
using mm28d by fast
moreover have "... = real (card G) - card (?p aa \<inter> (?p a))" using assms mm48 
by (metis (lifting, mono_tags))
ultimately show ?thesis by presburger
qed

lemma mm66e: "LinearCompletion bids N G = graph (N \<times> (Pow G-{{}})) (test bids)" 
unfolding graph_def using mm66 by blast
lemma ll33b: assumes "x\<in>X" shows "toFunction (graph X f) x = f x" using assms 
by (metis ll33 toFunction_def)
corollary ll33c: assumes "pair \<in> N \<times> (Pow G-{{}})" shows "linearCompletion' bids N G pair=test bids pair"
using assms ll33b mm66e by (metis(mono_tags))

lemma lm031: "test (real \<circ> ((bids:: _ => nat))) pair = real (test bids pair)" (is "?L=?R")
by simp
lemma lm031b: assumes "pair \<in> N \<times> (Pow G-{{}})" shows 
"linearCompletion' (real\<circ>(bids:: _ => nat)) N G pair = real (linearCompletion' bids N G pair)" 
using assms ll33c lm031 by (metis(no_types))
corollary lm031c: assumes "X \<subseteq> N \<times> (Pow G - {{}})" shows "\<forall>pair \<in> X. 
linearCompletion' (real \<circ> (bids::_=>nat)) N G pair= (real \<circ> (linearCompletion' bids N G)) pair"
using assms lm031b 
proof -
  { fix esk48\<^sub>0 :: "'a \<times> 'b set"
    { assume "esk48\<^sub>0 \<in> N \<times> (Pow G - {{}})"
      hence "linearCompletion' (real \<circ> bids) N G esk48\<^sub>0 = real (linearCompletion' bids N G esk48\<^sub>0)" using lm031b by blast
      hence "esk48\<^sub>0 \<notin> X \<or> linearCompletion' (real \<circ> bids) N G esk48\<^sub>0 = (real \<circ> linearCompletion' bids N G) esk48\<^sub>0" by simp }
    hence "esk48\<^sub>0 \<notin> X \<or> linearCompletion' (real \<circ> bids) N G esk48\<^sub>0 = (real \<circ> linearCompletion' bids N G) esk48\<^sub>0" using assms by blast }
  thus "\<forall>pair\<in>X. linearCompletion' (real \<circ> bids) N G pair = (real \<circ> linearCompletion' bids N G) pair" by blast
qed

corollary lm031e: assumes "aa \<subseteq> N \<times> (Pow G-{{}})" shows
"setsum ((linearCompletion' (real \<circ> (bids::_=>nat)) N G)) aa = real (setsum ((linearCompletion' bids N G)) aa)" 
(is "?L=?R")
proof -
have "\<forall> pair \<in> aa. linearCompletion' (real \<circ> bids) N G pair = (real \<circ> (linearCompletion' bids N G)) pair"
using assms by (rule lm031c)
then have "?L = setsum (real\<circ>(linearCompletion' bids N G)) aa" using setsum.cong by force
then show ?thesis by simp
qed

corollary lm031d: assumes "aa \<in> possibleAllocationsRel N G" shows
"setsum ((linearCompletion' (real \<circ> (bids::_=>nat)) N G)) aa = real (setsum ((linearCompletion' bids N G)) aa)" 
using assms lm031e mm63c by (metis(lifting,mono_tags))

corollary mm70b: 
assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
shows (* int (setsum (tiebids' a N G) a) - int (setsum (tiebids' a N G) aa) *)
"real (setsum (tiebids' a N G) a) - setsum (tiebids' a N G) aa = 
real (card G) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" (is "?L=?R")
proof -
  let ?l=linearCompletion' let ?m=maxbid' let ?s=setsum let ?p=pseudoAllocation
  let ?bb="?m a N G" let ?b="real \<circ> (?m a N G)"  
  have "real (?s ?bb (?p a)) - (?s ?bb (?p aa)) = ?R" using assms mm49b by blast 
  then have "?R = real (?s ?bb (?p a)) - (?s ?bb (?p aa))" by presburger
  have " ?s (?l ?b N G) aa = ?s ?b (?p aa)" using assms mm69 by blast moreover have 
  "... = ?s ?bb (?p aa)" by fastforce 
moreover have "(?s (?l ?b N G) aa) = real (?s (?l ?bb N G) aa)" using assms(3) by (rule lm031d)
(*  ultimately have "real (?s ?bb (?p a)) - (?s ?bb (?p aa)) = real (?s ?bb (?p a)) - (?s (?l ?bb N G) aa)"
  try0 *)
ultimately have 
  1: "?R = real (?s ?bb (?p a)) - (?s (?l ?bb N G) aa)" 
by (metis `real (card G) - real (card (pseudoAllocation aa \<inter> pseudoAllocation a)) = real (setsum (pseudoAllocation a <| (N \<times> finestpart G)) (pseudoAllocation a)) - real (setsum (pseudoAllocation a <| (N \<times> finestpart G)) (pseudoAllocation aa))`)
  have "?s (?l ?b N G) a=(?s ?b (?p a))" using assms mm69 by blast
  moreover have "... = ?s ?bb (?p a)" by force
  moreover have "... = real (?s ?bb (?p a))" by fast
  moreover have "?s (?l ?b N G) a = real (?s (?l ?bb N G) a)" using assms(2) by (rule lm031d)
  ultimately have "?s (?l ?bb N G) a = real (?s ?bb (?p a))" try0
by presburger
  thus ?thesis using 1 by presburger
qed

corollary mm70c: assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
"x=real (setsum (tiebids' a N G) a) - setsum (tiebids' a N G) aa" shows
"x <= card G & x \<ge> 0 & (x=0 \<longleftrightarrow> a = aa) & (aa \<noteq> a \<longrightarrow> setsum (tiebids' a N G) aa < setsum (tiebids' a N G) a)"
proof -
let ?p=pseudoAllocation have "real (card G) >= real (card G) - card (?p aa \<inter> (?p a))" by force
moreover have 
"real (setsum (tiebids' a N G) a) - setsum (tiebids' a N G) aa = 
real (card G) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))"
using assms mm70b by blast ultimately have
4: "x=real(card G)-card(pseudoAllocation aa\<inter>(pseudoAllocation a))" using assms by force then have
1: "x \<le> real (card G)" using assms by linarith have 
0: "card (?p aa) = card G & card (?p a) = card G" using assms mm48 by blast 
moreover have "finite (?p aa) & finite (?p a)" using assms mm54 by blast ultimately
have "card (?p aa \<inter> ?p a) \<le> card G" using Int_lower2 card_mono by fastforce then have 
2: "x \<ge> 0" using assms mm70b 4 by linarith 
have "card (?p aa \<inter> (?p a)) = card G \<longleftrightarrow> (?p aa = ?p a)" 
using 0 mm56 4 assms by (metis (lifting, mono_tags))
moreover have "?p aa = ?p a \<longrightarrow> a = aa" using assms mm75j inj_on_def 
by (metis (lifting, mono_tags))
ultimately have "card (?p aa \<inter> (?p a)) = card G \<longleftrightarrow> (a=aa)" by blast
moreover have "x = real (card G) - card (?p aa \<inter> (?p a))" using assms mm70b by blast
ultimately have 
3: "x = 0 \<longleftrightarrow> (a=aa)" by linarith then have 
"aa \<noteq> a \<longrightarrow> setsum (tiebids' a N G) aa < real (setsum (tiebids' a N G) a)" using 1 2 assms 
by auto
thus ?thesis using 1 2 3 by force
qed 

corollary mm70d: assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
"aa \<noteq> a" shows "setsum (tiebids' a N G) aa < setsum (tiebids' a N G) a" using assms mm70c by blast

lemma mm81: assumes
"N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}"
"aa \<in> (possibleAllocationsRel N (set G))-{chosenAllocation' N G bids random}" shows 
"setsum (resolvingBid' N G bids random) aa < setsum (resolvingBid' N G bids random) (chosenAllocation' N G bids random)" 
proof -
let ?a="chosenAllocation' N G bids random" let ?p=possibleAllocationsRel let ?G="set G"
have "?a \<in> winningAllocationsRel N (set G) bids" using assms mm82 by blast
moreover have "winningAllocationsRel N (set G) bids \<subseteq> ?p N ?G" using assms lm03 by metis
ultimately have "?a \<in> ?p N ?G" using mm82 assms lm03 set_rev_mp by blast
then show ?thesis using assms mm70d by blast 
qed

abbreviation "terminatingAuctionRel N G bids random == 
argmax (setsum (resolvingBid' N G bids random)) (argmax (setsum bids) (possibleAllocationsRel N (set G)))"

text{* Termination theorem: it assures that the number of winning allocations is exactly one *}
theorem mm92: assumes 
"N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" (*MC: why does this emerge only now? *) 
shows "terminatingAuctionRel N G (bids) random = {chosenAllocation' N G bids random}"
proof -
let ?p=possibleAllocationsRel let ?G="set G" 
let ?X="argmax (setsum bids) (?p N ?G)"
let ?a="chosenAllocation' N G bids random" let ?b="resolvingBid' N G bids random"
let ?f="setsum ?b" let ?ff="setsum ?b" 
let ?t=terminatingAuctionRel have "\<forall>aa\<in>(possibleAllocationsRel N ?G)-{?a}.  ?f aa < ?f ?a" 
using assms mm81 by blast then have 
0: "\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a" using assms mm81 by auto
have "finite N" using assms by simp then 
have "finite (?p N ?G)" using assms lm59 by (metis List.finite_set)
then have "finite ?X" using assms by (metis finite_subset lm03)
moreover have "?a \<in> ?X" using mm82 assms by blast
ultimately have 
"finite ?X & ?a \<in> ?X & (\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a)" using 0 by force
moreover have "(finite ?X & ?a \<in> ?X & (\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a)) \<longrightarrow> argmax ?f ?X = {?a}"
by (rule mm80c)
ultimately have "{?a} = argmax ?f ?X" using mm80 by presburger
moreover have "... = ?t N G bids random" by simp
ultimately show ?thesis by presburger
qed

text {* A more computable adaptor from set-theoretical to HOL function, with fallback value *}
abbreviation "toFunctionWithFallback2 R fallback == (% x. if (x \<in> Domain R) then (R,,x) else fallback)"
notation toFunctionWithFallback2 (infix "Elsee" 75) (* MC: This is computable, `Else' is not *)

section {* Combinatorial auction input examples *}

end

