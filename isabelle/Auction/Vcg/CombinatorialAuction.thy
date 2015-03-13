(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Author: Marco B. Caminati http://caminati.co.nr

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* VCG auction: definitions and theorems *}

theory CombinatorialAuction

imports
(* Complex *)
UniformTieBreaking
"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int" 
(* "~~/src/HOL/Library/Code_Binary_Nat" *)
"~~/src/HOL/Library/Code_Numeral"

begin

section {* Definition of a VCG auction scheme, through the pair @{term "(vcga', vcgp)"} *}

type_synonym bidvector' = "((participant \<times> goods) \<times> price) set"
abbreviation "participants b' == Domain (Domain b')"
abbreviation "seller == (0::integer)"
abbreviation "allAllocations N G == possibleAllocationsRel N G"
abbreviation "allAllocations' N \<Omega> == injectionsUniverse \<inter> 
{a. Domain a \<subseteq> N & Range a \<in> all_partitions \<Omega>}" 
abbreviation "allAllocations'' N G == allocationsUniverse\<inter>{a. Domain a \<subseteq> N & \<Union> Range a = G}"
lemma lm28: "allAllocations N G=allAllocations' N G & 
allAllocations N G=allAllocations'' N G" using lm19 nn24 by metis
lemma lm28b: 
"(a \<in> allAllocations'' N G) = (a \<in> allocationsUniverse& Domain a \<subseteq> N & \<Union> Range a = G)" by force
abbreviation "soldAllocations N \<Omega> == 
(Outside' {seller}) ` (allAllocations (N \<union> {seller}) \<Omega>)"
abbreviation "soldAllocations' N \<Omega> == 
(Outside' {seller}) ` (allAllocations' (N \<union> {seller}) \<Omega>)"
abbreviation "soldAllocations'' N \<Omega> == 
(Outside' {seller}) ` (allAllocations'' (N \<union> {seller}) \<Omega>)"
lemma lm28c: 
"soldAllocations N G = soldAllocations' N G & soldAllocations' N G = soldAllocations'' N G"
using assms lm28 by metis
corollary lm28d: "soldAllocations = soldAllocations' & soldAllocations' = soldAllocations''
& soldAllocations = soldAllocations''" using lm28c by metis
lemma lm32: "soldAllocations (N-{seller}) G \<subseteq> soldAllocations N G" using Outside_def by simp

lemma lm34: "(a \<in> allocationsUniverse) = (a \<in> allAllocations'' (Domain a) (\<Union> Range a))"
by blast
lemma lm35: assumes "N1 \<subseteq> N2" shows "allAllocations'' N1 G \<subseteq> allAllocations'' N2 G" 
using assms by auto
lemma lm36: assumes "a \<in> allAllocations'' N G" shows "Domain (a -- x) \<subseteq> N-{x}" 
using assms Outside_def by fastforce
lemma lm37: assumes "a \<in> soldAllocations N G" shows "a \<in> allocationsUniverse"
proof -
obtain aa where "a=aa -- seller & aa \<in> allAllocations (N\<union>{seller}) G"
using assms by blast
then have "a \<subseteq> aa & aa \<in> allocationsUniverse" unfolding Outside_def using nn24b by blast
then show ?thesis using lm35b by blast
qed
lemma lm38: assumes "a \<in> soldAllocations N G" shows "a \<in> allAllocations'' (Domain a) (\<Union>Range a)"
proof - show ?thesis using assms lm37 by blast qed
lemma  assumes "N1 \<subseteq> N2" shows "soldAllocations'' N1 G \<subseteq> soldAllocations'' N2 G"
using assms lm35 lm36  nn24c lm28b lm28 lm34 lm38 Outside_def by blast
(*
lemma lm39a: "{} \<in> injectionsUniverse" by (metis converse_empty mem_Collect_eq runiq_emptyrel)
lemma lm39b: "{} \<in> partitionValuedUniverse" by (metis (lifting) Pow_bottom UN_iff lm36b)
lemma "{} \<in> allocationsUniverse" 
by (metis nn39)
 corollary lm39: "{} \<in> allocationsUniverse" using lm39a lm39b by blast
*)
lemma lll59b: "runiq (X\<times>{y})" using lll59 by (metis trivial_singleton)
lemma lm37b: "{x}\<times>{y} \<in> injectionsUniverse" using Universes.lm37 by fastforce
lemma lm40b: assumes "a \<in> soldAllocations'' N G" shows "\<Union> Range a \<subseteq> G" using assms Outside_def by blast
lemma lm41: "a \<in> soldAllocations'' N G = 
(EX aa. aa -- (seller)=a & aa\<in>allAllocations'' (N \<union> {seller}) G)" by blast

lemma lm18: "(R +* ({x}\<times>Y)) -- x = R -- x" unfolding Outside_def paste_def by blast

lemma lm37e: assumes "a \<in> allocationsUniverse" "Domain a \<subseteq> N-{seller}" "\<Union> Range a \<subseteq> G" shows
"a \<in> soldAllocations'' N G" using assms lm41 
proof -
let ?i="seller" let ?Y="{G-\<Union> Range a}-{{}}" let ?b="{?i}\<times>?Y" let ?aa="a\<union>?b"
let ?aa'="a +* ?b" 
have
1: "a \<in> allocationsUniverse" using assms(1) by fast 
have "?b \<subseteq> {(?i,G-\<Union> Range a)} - {(?i, {})}" by fastforce then have 
2: "?b \<in> allocationsUniverse" using Universes.lm38 lm35b by (metis(no_types)) have 
3: "\<Union> Range a \<inter> \<Union> (Range ?b) = {}" by blast have 
4: "Domain a \<inter> Domain ?b ={}" using assms by fast
have "?aa \<in> allocationsUniverse" using 1 2 3 4 by (rule lm23)
then have "?aa \<in> allAllocations'' (Domain ?aa) 
(\<Union> Range ?aa)" unfolding lm34 by metis then have 
"?aa \<in> allAllocations'' (N\<union>{?i}) (\<Union> Range ?aa)" using lm35 assms paste_def by auto
moreover have "Range ?aa = Range a \<union> ?Y" by blast then moreover have 
"\<Union> Range ?aa = G" using Un_Diff_cancel Un_Diff_cancel2 Union_Un_distrib Union_empty Union_insert  
by (metis (lifting, no_types) assms(3) cSup_singleton subset_Un_eq) moreover have 
"?aa' = ?aa" using 4 by (rule paste_disj_domains)
ultimately have "?aa' \<in> allAllocations'' (N\<union>{?i}) G" by simp
moreover have "Domain ?b \<subseteq> {?i}" by fast 
have "?aa' -- ?i = a -- ?i" (*MC: why don't I need "moreover" here? *) by (rule lm18)
moreover have "... = a" using Outside_def assms(2) by auto 
ultimately show ?thesis using lm41 by auto
qed

lemma lm23: 
"a\<in>allAllocations N \<Omega>=(a\<in>injectionsUniverse & Domain a\<subseteq>N & Range a\<in>all_partitions \<Omega>)" 
by (metis (full_types) lm19c)

lemma lm37n: assumes "a \<in> soldAllocations'' N G" shows "Domain a \<subseteq> N-{seller} & a \<in> allocationsUniverse"  
proof -
let ?i="seller" obtain aa where
0: "a=aa -- ?i & aa \<in> allAllocations'' (N \<union> {?i}) G" using assms(1) lm41 by blast
then have "Domain aa \<subseteq> N \<union> {?i}" using lm23 by blast
then have "Domain a \<subseteq> N - {?i}" using 0 Outside_def by blast
moreover have "a \<in> soldAllocations N G" using assms lm28d by metis
then moreover have "a \<in> allocationsUniverse" using lm37 by blast
ultimately show ?thesis by blast
qed

corollary lm37c: assumes "a \<in> soldAllocations'' N G" shows 
"a \<in> allocationsUniverse & Domain a \<subseteq> N-{seller} & \<Union> Range a \<subseteq> G"
proof -
have "a \<in> allocationsUniverse" using assms lm37n by blast
moreover have "Domain a \<subseteq> N-{seller}" using assms lm37n by blast
moreover have "\<Union> Range a \<subseteq> G" using assms lm40b by blast
ultimately show ?thesis by blast
qed

corollary lm37d: 
"(a\<in>soldAllocations'' N G)=(a\<in>allocationsUniverse& Domain a \<subseteq> N-{seller} & \<Union> Range a \<subseteq> G)" 
using lm37c lm37e by (metis (mono_tags))

lemma lm42: "(a\<in>allocationsUniverse& Domain a \<subseteq> N-{seller} & \<Union> Range a \<subseteq> G) = 
(a\<in>allocationsUniverse& a\<in>{aa. Domain aa \<subseteq> N-{seller} & \<Union> Range aa \<subseteq> G})" 
by (metis (lifting, no_types) mem_Collect_eq)

corollary lm37f: "(a\<in>soldAllocations'' N G)=
(a\<in>allocationsUniverse& a\<in>{aa. Domain aa \<subseteq> N-{seller} & \<Union> Range aa \<subseteq> G})" (is "?L = ?R") 
proof -
  have "?L = (a\<in>allocationsUniverse& Domain a \<subseteq> N-{seller} & \<Union> Range a \<subseteq> G)" by (rule lm37d)
  moreover have "... = ?R" by (rule lm42) ultimately show ?thesis by presburger
qed

corollary lm37g: "a\<in>soldAllocations'' N G=
(a\<in> (allocationsUniverse \<inter> {aa. Domain aa \<subseteq> N-{seller} & \<Union> Range aa \<subseteq> G}))" 
using lm37f by (metis (mono_tags) Int_iff)

abbreviation "soldAllocations''' N G == 
allocationsUniverse\<inter>{aa. Domain aa\<subseteq>N-{seller} & \<Union>Range aa\<subseteq>G}"

lemma lm44: assumes "a \<in> soldAllocations''' N G" shows "a -- n \<in> soldAllocations''' (N-{n}) G"
proof -
  let ?bb=seller let ?d=Domain let ?r=Range let ?X2="{aa. ?d aa\<subseteq>N-{?bb} & \<Union>?r aa\<subseteq>G}" 
  let ?X1="{aa. ?d aa\<subseteq>N-{n}-{?bb} & \<Union>?r aa\<subseteq>G}" 
  have "a\<in>?X2" using assms(1) by fast then have 
  0: "?d a \<subseteq> N-{?bb} & \<Union>?r a \<subseteq> G" by blast then have "?d (a--n) \<subseteq> N-{?bb}-{n}" 
  using outside_reduces_domain by (metis Diff_mono subset_refl) moreover have 
  "... = N-{n}-{?bb}" by fastforce ultimately have 
  "?d (a--n) \<subseteq> N-{n}-{?bb}" by blast moreover have "\<Union> ?r (a--n) \<subseteq> G" 
  unfolding Outside_def using 0 by blast ultimately have "a -- n \<in> ?X1" by fast moreover have 
  "a--n \<in> allocationsUniverse" using assms(1) Int_iff lm35d by (metis(lifting,mono_tags)) 
  ultimately show ?thesis by blast
qed

corollary lm37h: "soldAllocations'' N G=soldAllocations''' N G"
(is "?L=?R") proof - {fix a have "a \<in> ?L = (a \<in> ?R)" by (rule lm37g)} thus ?thesis by blast qed

lemma lm28e: "soldAllocations=soldAllocations' & soldAllocations'=soldAllocations'' &
soldAllocations''=soldAllocations'''" using lm37h lm28d by metis

corollary lm44b: assumes "a \<in> soldAllocations N G" shows "a -- n \<in> soldAllocations (N-{n}) G"
(* MC: being an allocation is invariant to subtracting any single bidder 
This is the fundamental step to prove non-negativity of vcgp *)
proof - 
let ?A'=soldAllocations''' have "a \<in> ?A' N G" using assms lm28e by metis then
have "a -- n \<in> ?A' (N-{n}) G" by (rule lm44) thus ?thesis using lm28e by metis 
qed

corollary lm37i: assumes "G1 \<subseteq> G2" shows "soldAllocations''' N G1 \<subseteq> soldAllocations''' N G2"
using assms by blast

corollary lm33: assumes "G1 \<subseteq> G2" shows "soldAllocations'' N G1 \<subseteq> soldAllocations'' N G2"
using assms lm37i lm37h 
proof -
have "soldAllocations'' N G1 = soldAllocations''' N G1" by (rule lm37h)
moreover have "... \<subseteq> soldAllocations''' N G2" using assms(1) by (rule lm37i)
moreover have "... = soldAllocations'' N G2" using lm37h by metis
ultimately show ?thesis by auto
qed

abbreviation "maximalAllocations'' N \<Omega> b == argmax (setsum b) (soldAllocations N \<Omega>)"

abbreviation "maximalStrictAllocations' N G b==
argmax (setsum b) (allAllocations ({seller}\<union>N) G)"
(*MC: these are the allocations maximizing the revenue, and also including the unallocated goods assigned to
the virtual participant addedBidder. 
Note that commonly b is set to zero identically for such bidder, but this is not formally imposed here.*)
(*abbreviation "allAllocations N G == possibleAllocationsAlg3 N G"
abbreviation "maximalAllocations G b == argmaxList (setsum' b) ((allAllocations (Participants b) G))"
*)

corollary lm43d: assumes "a \<in> allocationsUniverse" shows 
"(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> allocationsUniverse" using assms lm43b 
by fastforce

(* lemma lm27c: "seller \<notin> int `N" by fastforce *)

abbreviation "randomBids' N \<Omega> b random==resolvingBid' (N\<union>{seller}) \<Omega> b random"

(* abbreviation "vcgas N G b r  ==    (argmax (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b))"*)

abbreviation "vcgas N G b r  == Outside' {seller} ` 
   ((argmax\<circ>setsum) (randomBids' N G b r)
    ((argmax\<circ>setsum) b (allAllocations (N\<union>{seller}) (set G))))"
abbreviation "vcga N G b r == the_elem (vcgas N G b r)"
abbreviation "vcga' N G b r == (the_elem
(argmax (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b))) -- seller"

lemma lm001: assumes 
"card ((argmax\<circ>setsum) (randomBids' N G b r) ((argmax\<circ>setsum) b (allAllocations (N\<union>{seller}) (set G))))=1" 
shows "vcga N G b r = 
(the_elem
((argmax\<circ>setsum) (randomBids' N G b r) ((argmax\<circ>setsum) b (allAllocations ({seller}\<union>N) (set G))))) -- seller"
using assms lm012 by auto

corollary lm001b: assumes 
"card ((argmax\<circ>setsum) (randomBids' N G b r) ((argmax\<circ>setsum) b (allAllocations (N\<union>{seller}) (set G))))=1"
shows "vcga N G b r = vcga' N G b r" (is "?l=?r") using assms lm001
proof -
have "?l=(the_elem ((argmax\<circ>setsum) (randomBids' N G b r) 
((argmax\<circ>setsum) b (allAllocations ({seller}\<union>N) (set G))))) -- seller"
using assms by (rule lm001) moreover have "... = ?r" by force ultimately show ?thesis by blast
qed

lemma lm92c: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"card (
(argmax\<circ>setsum) (randomBids' N G bids random)
    ((argmax\<circ>setsum) bids (allAllocations (N\<union>{seller}) (set G))))=1" (is "card ?l=_")
proof - 
  let ?N="N\<union>{seller}" let ?b'="randomBids' N G bids random" let ?s=setsum let ?a=argmax let ?f="?a \<circ> ?s"
  have 1: "?N\<noteq>{}" by auto have 4: "finite ?N" using assms(3) by simp
  have "?a (?s ?b') (?a (?s bids) (allAllocations ?N (set G)))=
  {chosenAllocation' ?N G bids random}" (is "?L=?R")
  using 1 assms(1) assms(2) 4 by (rule lm92)
  moreover have "?L= ?f ?b' (?f bids (allAllocations ?N (set G)))" by auto
  ultimately have "?l={chosenAllocation' ?N G bids random}" by presburger
  moreover have "card ...=1" by simp ultimately show ?thesis by presburger 
qed

lemma lm002: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"vcga N G b r = vcga' N G b r" (is "?l=?r") using assms lm001b lm92c by blast

theorem vcgaDefiniteness: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"card (vcgas N G b r)=1"
using assms lm92c lm011 (* by blast: MC made explicit to paper-comment it *)
proof -
have "card ((argmax\<circ>setsum) (randomBids' N G b r) ((argmax\<circ>setsum) b (allAllocations (N\<union>{seller}) (set G))))=1" 
(is "card ?X=_") using assms lm92c by blast
moreover have "(Outside'{seller}) ` ?X = vcgas N G b r" by blast
ultimately show ?thesis using lm011 by blast
qed

theorem vcgpDefiniteness: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"\<exists>! y. vcgap N G b r n=y" using assms vcgaDefiniteness by simp

text {* Here we are showing that our way of randomizing using randomBids' actually breaks the tie:
we are left with a singleton after the tie-breaking step. *}

lemma lm92b: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"card (argmax (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b))=1"
(is "card ?L=_")
(*"card (vcgas N G b r) = 1"*)
proof -
let ?n="{seller}" have 
1: "(?n \<union> N)\<noteq>{}" by simp have 
4: "finite (?n\<union>N)" using assms(3) by fast have 
"terminatingAuctionRel (?n\<union>N) G b r = {chosenAllocation' (?n\<union>N) G b r}" using 1 assms(1) 
assms(2) 4 by (rule lm92) moreover have "?L = terminatingAuctionRel (?n\<union>N) G b r" by auto
ultimately show ?thesis by auto
qed

lemma "argmax (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b) \<subseteq> 
maximalStrictAllocations' N (set G) b" by auto

corollary lm58: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"the_elem
(argmax (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b)) \<in>
(maximalStrictAllocations' N (set G) b)" (is "the_elem ?X \<in> ?R") using assms lm92b lm57
proof -
have "card ?X=1" using assms by (rule lm92b) moreover have "?X \<subseteq> ?R" by auto
ultimately show ?thesis using nn57b by blast
qed

corollary lm58b: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga' N G b r \<in> (Outside' {seller})`(maximalStrictAllocations' N (set G) b)"
using assms lm58 by blast

lemma lm62: "(Outside' {seller})`(maximalStrictAllocations' N G b) \<subseteq> soldAllocations N G"
using Outside_def by force

theorem lm58d: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga' N G b r \<in> soldAllocations N (set G)" (is "?a \<in> ?A") using assms lm58b lm62 
proof - have "?a \<in> (Outside' {seller})`(maximalStrictAllocations' N (set G) b)" 
using assms by (rule lm58b) thus ?thesis using lm62  by fastforce qed
corollary lm58f: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga N G b r \<in> soldAllocations N (set G)" (is "_\<in>?r") 
proof - have "vcga' N G b r \<in> ?r" using assms by (rule lm58d) then show ?thesis using assms lm002 by blast qed

corollary lm59b: assumes "\<forall>X. X \<in> Range a \<longrightarrow>b (seller, X)=0" "finite a" shows 
"setsum b a = setsum b (a--seller)"
proof -
let ?n=seller have "finite (a||{?n})" using assms restrict_def by (metis finite_Int) 
moreover have "\<forall>z \<in> a||{?n}. b z=0" using assms restrict_def by fastforce
ultimately have "setsum b (a||{?n}) = 0" using assms by (metis setsum.neutral)
thus ?thesis using nn59 assms(2) by (metis comm_monoid_add_class.add.right_neutral)
qed

corollary lm59c: assumes "\<forall>a\<in>A. finite a & (\<forall> X. X\<in>Range a \<longrightarrow> b (seller, X)=0)"
shows "{setsum b a| a. a\<in>A}={setsum b (a -- seller)| a. a\<in>A}" using assms lm59b 
by (metis (lifting, no_types))
corollary lm58c: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"EX a. ((a \<in> (maximalStrictAllocations' N (set G) b)) 
& (vcga' N G b r = a -- seller) 
& (a \<in> argmax (setsum b) (allAllocations ({seller}\<union>N) (set G)))
)" (is "EX a. _ & _ & a \<in> ?X")
using assms lm58b argmax_def by fast

lemma assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"\<forall>aa\<in>allAllocations ({seller}\<union>N) (set G). finite aa"
using assms by (metis List.finite_set UniformTieBreaking.lm44)

lemma lm61: assumes "distinct G" "set G \<noteq> {}" "finite N" 
"\<forall>aa\<in>allAllocations ({seller}\<union>N) (set G). \<forall> X \<in> Range aa. b (seller, X)=0"
(is "\<forall>aa\<in>?X. _") shows "setsum b (vcga' N G b r)=Max{setsum b aa| aa. aa \<in> soldAllocations N (set G)}"
proof -
let ?n=seller let ?s=setsum let ?a="vcga' N G b r" obtain a where 
0: "a \<in> maximalStrictAllocations' N (set G) b & ?a=a--?n & 
(a\<in>argmax (setsum b) (allAllocations({seller}\<union>N)(set G)))"(is "_ & ?a=_ & a\<in>?Z")
using assms(1,2,3) lm58c by blast have 
1: "\<forall>aa\<in>?X. finite aa & (\<forall> X. X\<in>Range aa \<longrightarrow> b (?n, X)=0)" using assms(4) 
List.finite_set UniformTieBreaking.lm44 by metis have 
2: "a \<in> ?X" using 0 by auto have "a \<in> ?Z" using 0 by fast 
then have "a \<in> ?X\<inter>{x. ?s b x = Max (?s b ` ?X)}" using lm78 by simp
then have "a \<in> {x. ?s b x = Max (?s b ` ?X)}" using lm78 by simp
moreover have "?s b ` ?X = {?s b aa| aa. aa\<in>?X}" by blast
ultimately have "?s b a = Max {?s b aa| aa. aa\<in>?X}" by auto
moreover have "{?s b aa| aa. aa\<in>?X} = {?s b (aa--?n)| aa. aa\<in>?X}" using 1 by (rule lm59c)
moreover have "... = {?s b aa| aa. aa \<in> Outside' {?n}`?X}" by blast
moreover have "... = {?s b aa| aa. aa \<in> soldAllocations N (set G)}" by simp
ultimately have "Max {?s b aa| aa. aa \<in> soldAllocations N (set G)} = ?s b a" by presburger
moreover have "... = ?s b (a--?n)" using 1 2 lm59b by (metis (lifting, no_types))
ultimately show "?s b ?a=Max{?s b aa| aa. aa \<in> soldAllocations N (set G)}" using 0 by presburger
qed

























































text {* Adequacy theorem: the allocation satisfies the standard pen-and-paper specification of a VCG auction.
See, for example, \cite[\S~1.2]{cramton}. *}
theorem lm61b: assumes "distinct G" "set G \<noteq> {}" "finite N" "\<forall> X. b (seller, X)=0" 
shows "setsum b (vcga' N G b r)=Max{setsum b aa| aa. aa \<in> soldAllocations N (set G)}"
using assms lm61 by blast

corollary lm58e: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"vcga' N G b r \<in> allocationsUniverse & \<Union> Range (vcga' N G b r) \<subseteq> set G" using assms lm58b 
proof -
let ?a="vcga' N G b r" let ?n=seller
obtain a where 
0: "?a=a -- seller & a \<in> maximalStrictAllocations' N (set G) b"
using assms lm58b by blast
then moreover have 
1: "a \<in> allAllocations ({?n}\<union>N) (set G)" by auto
moreover have "maximalStrictAllocations' N (set G) b \<subseteq> allocationsUniverse" 
by (metis (lifting, mono_tags) UniformTieBreaking.lm03 Universes.lm50 subset_trans)
ultimately moreover have "?a=a -- seller & a \<in> allocationsUniverse" by blast
then have "?a \<in> allocationsUniverse" using lm35d by auto
moreover have "\<Union> Range a= set G" using nn24c 1 by metis
then moreover have "\<Union> Range ?a \<subseteq> set G" using Outside_def 0 by fast
ultimately show ?thesis using lm35d Outside_def by blast
qed

lemma "vcga' N G b r = the_elem ((argmax \<circ> setsum) (randomBids' N G b r) 
((argmax \<circ> setsum) b (allAllocations ({seller}\<union>N) (set G)))) -- seller" by simp

abbreviation "vcgp N G b r n ==
Max (setsum b ` (soldAllocations (N-{n}) (set G))) - (setsum b (vcga N G b r -- n))"

lemma lm63: assumes "x \<in> X" "finite X" shows "Max (f`X) >= f x" (is "?L >= ?R") using assms 
by (metis (hide_lams, no_types) Max.coboundedI finite_imageI image_eqI)

lemma lm59: assumes "finite N" "finite G" shows "finite (soldAllocations N G)" using assms lm59
finite.emptyI finite.insertI finite_UnI finite_imageI by metis

text{* The price paid by any participant is non-negative. *}
theorem NonnegPrices: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcgp N G b r n >= (0::price)" 
proof - 
let ?a="vcga N G b r" let ?A=soldAllocations let ?f="setsum b" 
have "?a \<in> ?A N (set G)" using assms by (rule lm58f)
then have "?a -- n \<in> ?A (N-{n}) (set G)" by (rule lm44b)
moreover have "finite (?A (N-{n}) (set G))" using assms(3) lm59 finite_set finite_Diff by blast
ultimately have "Max (?f`(?A (N-{n}) (set G))) \<ge> ?f (?a -- n)" (is "?L >= ?R") by (rule lm63)
then show "?L - ?R >=0" by linarith
qed

lemma lm19b: "allAllocations N G = possibleAllocationsRel N G" using assms by (metis lm19)
abbreviation "strictAllocationsUniverse == allocationsUniverse"

abbreviation "Goods bids == \<Union>((snd\<circ>fst)`bids)"

corollary lm45: assumes "a \<in> soldAllocations''' N G" shows "Range a \<in> partitionsUniverse" 
using assms by (metis (lifting, mono_tags) Int_iff lm22 mem_Collect_eq)

corollary lm45a: assumes "a \<in> soldAllocations N G" shows "Range a \<in> partitionsUniverse"
proof - have "a \<in> soldAllocations''' N G" using assms lm28e by metis thus ?thesis by (rule lm45) qed

corollary assumes 
"N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" (*MC: why does this emerge only now? *) 
shows "(Outside' {seller}) ` (terminatingAuctionRel N G (bids) random) = 
{chosenAllocation' N G bids random -- (seller)}" (is "?L=?R") using assms lm92 Outside_def 
proof -
have "?R = Outside' {seller} ` {chosenAllocation' N G bids random}" using Outside_def 
by blast 
moreover have "... = (Outside'{seller})`(terminatingAuctionRel N G bids random)" using assms lm92 
by blast
ultimately show ?thesis by presburger
qed

(* abbreviation "argMax X f == argmax f X" *)
lemma "terminatingAuctionRel N G b r = 
((argmax (setsum (resolvingBid' N G b (r)))) \<circ> (argmax (setsum b)))
(possibleAllocationsRel N (set G))" by force
term "(Union \<circ> (argmax (setsum (resolvingBid' N G b (r)))) \<circ> (argmax (setsum b)))
(possibleAllocationsRel N (set G))"

lemma "maximalStrictAllocations' N G b=winningAllocationsRel ({seller} \<union> N) G b" by fast

lemma lm64: assumes "a \<in> allocationsUniverse" 
"n1 \<in> Domain a" "n2 \<in> Domain a"
"n1 \<noteq> n2" 
shows "a,,n1 \<inter> a,,n2={}" using assms is_non_overlapping_def lm22 mem_Collect_eq 
proof - have "Range a \<in> partitionsUniverse" using assms lm22 by blast
moreover have "a \<in> injectionsUniverse & a \<in> partitionValuedUniverse" using assms by (metis (lifting, no_types) IntD1 IntD2)
ultimately moreover have "a,,n1 \<in> Range a" using assms 
by (metis (mono_tags) eval_runiq_in_Range mem_Collect_eq)
ultimately moreover have "a,,n1 \<noteq> a,,n2" using 
assms converse.intros eval_runiq_rel mem_Collect_eq runiq_basic by (metis (lifting, no_types))
ultimately show ?thesis using is_non_overlapping_def by (metis (lifting, no_types) assms(3) eval_runiq_in_Range mem_Collect_eq)
qed

lemma lm64c: assumes "a \<in> allocationsUniverse" 
"n1 \<in> Domain a" "n2 \<in> Domain a"
"n1 \<noteq> n2" 
shows "a,,,n1 \<inter> a,,,n2={}" using assms lm64 lll82 by fastforce 

text{* No good is assigned twice. *}
theorem PairwiseDisjointAllocations:
fixes n1::"participant" fixes G::"goods list" fixes N::"participant set"
assumes "distinct G" "set G \<noteq> {}" "finite N"  
(* "n1 \<in> Domain (vcga' N G b r)" "n2 \<in> Domain (vcga' N G b r)" *) 
"n1 \<noteq> n2" 
shows "(vcga' N G b r),,,n1 \<inter> (vcga' N G b r),,,n2={}"  
proof -
have "vcga' N G b r \<in> allocationsUniverse" using lm58e assms by blast
then show ?thesis using lm64c assms by fast
qed

lemma assumes "R,,,x \<noteq> {}" shows "x \<in> Domain R" using assms  
proof - have "\<Union> (R``{x}) \<noteq> {}" using assms(1) by fast
then have "R``{x} \<noteq> {}" by fast thus ?thesis by blast qed

lemma assumes "runiq f" and "x \<in> Domain f" shows "(f ,, x) \<in> Range f" using assms 
by (rule eval_runiq_in_Range)

text {* Nothing outside the set of goods is allocated. *}
theorem OnlyGoodsAllocated: assumes "distinct G" "set G \<noteq> {}" "finite N" "g \<in> (vcga N G b r),,,n" 
shows "g \<in> set G"
proof - 
let ?a="vcga' N G b r" have "?a \<in> allocationsUniverse" using assms(1,2,3) lm58e by blast
then have "runiq ?a" using assms(1,2,3) by blast
moreover have "n \<in> Domain ?a" using assms eval_rel_def lm002 by fast
ultimately moreover have "?a,,n \<in> Range ?a" using eval_runiq_in_Range by fast 
ultimately have "?a,,,n \<in> Range ?a" using lll82 by fastforce
then have "g \<in> \<Union> Range ?a" using assms lm002 by blast 
moreover have "\<Union> Range ?a \<subseteq> set G" using assms(1,2,3) lm58e by fast
ultimately show ?thesis by blast
qed

definition "allStrictAllocations N G == possibleAllocationsAlg N G"
abbreviation "maximalStrictAllocations N G b==
argmax (setsum b) (set (allStrictAllocations ({seller}\<union>N) G))"

definition "maximalStrictAllocations2 N G b=
argmax (setsum b) (set (allStrictAllocations ({seller}\<union>N) G))"

definition "chosenAllocation N G b (r::integer) == 
hd(perm2 (takeAll (%x. x\<in> (argmax \<circ> setsum) b (set (allStrictAllocations N G))) (allStrictAllocations N G)) (nat_of_integer r))"
definition "maxbid a N G == (bidMaximizedBy a N G) Elsee 0"
definition "linearCompletion bids N G == (LinearCompletion bids N G) Elsee 0"
definition "tiebids a N G == linearCompletion (maxbid a N G) N G"
definition "resolvingBid N G bids random == tiebids (chosenAllocation N G bids random) N (set G)"
definition "randomBids N \<Omega> b random==resolvingBid (N\<union>{seller}) \<Omega> b random"
definition "vcgaAlgWithoutLosers N G b r == (the_elem
(argmax (setsum (randomBids N G b r)) (maximalStrictAllocations N G b))) -- seller"
abbreviation "addLosers participantset allo==(participantset \<times> {{}}) +* allo"
definition "vcgaAlg N G b r = addLosers N (vcgaAlgWithoutLosers N G b r)"
abbreviation "allAllocationsComp N \<Omega> == 
(Outside' {seller}) ` set (allStrictAllocations (N \<union> {seller}) \<Omega>)"
definition "vcgpAlg N G b r n =
Max (setsum b ` (allAllocationsComp (N-{n}) G)) - (setsum b (vcgaAlgWithoutLosers N G b r -- n))"

lemma lm01: assumes "x \<in> Domain f" shows "toFunction f x = (f Elsee 0) x"
unfolding toFunctionWithFallback2_def
by (metis assms toFunction_def)
lemma lm03: "Domain (Y \<times> {0::nat}) = Y & Domain (X \<times> {1})=X" by blast
lemma lm04: "Domain (X <|| Y) = X \<union> Y" using lm03 paste_Domain sup_commute by metis
corollary lm04b: "Domain (bidMaximizedBy a N G) = pseudoAllocation a \<union> N \<times> (finestpart G)" using lm04 
by metis
lemma lm19: "(pseudoAllocation a) \<subseteq> Domain (bidMaximizedBy a N G)" by (metis lm04 Un_upper1)

lemma lm02: assumes "x \<in> (N \<times> (Pow G - {{}}))" shows 
"linearCompletion' b N G x=linearCompletion b N G x" unfolding linearCompletion_def 
using assms lm01 Domain.simps imageI by (metis(no_types,lifting))
(*lm64*)

(*
lemma assumes "a \<in> possibleAllocationsRel N G" shows "pseudoAllocation a \<subseteq> Domain (bidMaximizedBy a N G)" 
using assms sorry

corollary lm01b: "\<forall>x. x \<in>(pseudoAllocation aa) \<longrightarrow> ((bidMaximizedBy a N G) Elsee 0) x =
(toFunction (bidMaximizedBy a N G)) x" using assms lm01 lm19 sorry

corollary assumes 
"pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" "finite (pseudoAllocation aa)"
shows "setsum ((bidMaximizedBy a N G) Elsee 0) (pseudoAllocation a) - 
(setsum ((bidMaximizedBy a N G) Elsee 0) (pseudoAllocation aa)) = 
card (pseudoAllocation a) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" 
(is "?l1 - ?l2 = ?r") using lm28 assms lm49 lm04 lm05 Un_upper1 UnCI UnI1 
proof -
(* sledgehammer [isar_proofs=true,"try0"=true,smt_proofs=false,provers=z3] *)
have "pseudoAllocation aa \<subseteq> Domain (bidMaximizedBy a N G)" using lm04b assms(1) 
by metis
then have "\<forall> x \<in> pseudoAllocation aa. toFunction (bidMaximizedBy a N G) x = 
(bidMaximizedBy a N G Elsee 0) x" by (metis (erased, lifting) rev_subsetD toFunction_def)
then have "setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation aa) = ?l2"
using lm20 by fast
moreover have "?l1 = setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation a)"
using lm01b setsum.cong by fast
ultimately have "?l1 - ?l2 = setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation a) 
- setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation aa)" by presburger
moreover have "... = ?r" using assms lm49 lm28 by fast
ultimately show ?thesis by presburger
qed
*)

corollary lm20: assumes "\<forall>x \<in> X. f x = g x" shows "setsum f X = setsum g X" 
using assms setsum.cong by auto

lemma lm06: assumes "fst pair \<in> N" "snd pair \<in> Pow G - {{}}" shows "setsum (%g.
(toFunction (bidMaximizedBy a N G))
(fst pair, g)) (finestpart (snd pair)) =
setsum (%g. 
((bidMaximizedBy a N G) Elsee 0)
(fst pair, g)) (finestpart (snd pair))"
using assms lm01 lm05 lm04 Un_upper1 UnCI UnI1 setsum.cong lm55n Diff_iff Pow_iff in_mono
proof -
let ?f1="%g.(toFunction (bidMaximizedBy a N G))(fst pair, g)"
let ?f2="%g.((bidMaximizedBy a N G) Elsee 0)(fst pair, g)"
{ 
  fix g assume "g \<in> finestpart (snd pair)" then have 
  0: "g \<in> finestpart G" using assms lm55n by (metis Diff_iff Pow_iff in_mono)
  have "?f1 g = ?f2 g" 
  proof -
    have "\<And>x\<^sub>1 x\<^sub>2. (x\<^sub>1, g) \<in> x\<^sub>2 \<times> finestpart G \<or> x\<^sub>1 \<notin> x\<^sub>2" by (metis 0 mem_Sigma_iff) 
    then have "(pseudoAllocation a <| (N \<times> finestpart G)) (fst pair, g) = maxbid a N G (fst pair, g)"
    unfolding toFunctionWithFallback2_def maxbid_def
    by (metis (no_types) lm04 UnCI assms(1) toFunction_def)
    thus ?thesis unfolding maxbid_def by blast
  qed
}
thus ?thesis using setsum.cong by simp
qed

corollary lm07: assumes "pair \<in> N \<times> (Pow G - {{}})" shows 
"partialCompletionOf (toFunction (bidMaximizedBy a N G)) pair = 
partialCompletionOf ((bidMaximizedBy a N G) Elsee 0) pair" using assms lm06 
proof - 
have "fst pair \<in> N" using assms by force 
moreover have "snd pair \<in> Pow G - {{}}" using assms(1) by force
ultimately show ?thesis using lm06 by blast
qed

lemma lm08: assumes "\<forall>x \<in> X. f x = g x" shows "f`X=g`X" using assms by (metis image_cong)

corollary lm09: "\<forall> pair \<in> N \<times> (Pow G - {{}}).  
partialCompletionOf (toFunction (bidMaximizedBy a N G)) pair = 
partialCompletionOf ((bidMaximizedBy a N G) Elsee 0) pair" using lm07 
by blast  

corollary lm10: 
"(partialCompletionOf (toFunction (bidMaximizedBy a N G))) ` (N \<times> (Pow G - {{}}))=
(partialCompletionOf ((bidMaximizedBy a N G) Elsee 0)) ` (N \<times> (Pow G - {{}}))" (is "?f1 ` ?Z = ?f2 ` ?Z")
proof - (*MC: no way to automatize this trivial proof??!! *)
have "\<forall> z \<in> ?Z. ?f1 z = ?f2 z" by (rule lm09) thus ?thesis by (rule lm08)
qed

corollary lm11: "LinearCompletion (toFunction (bidMaximizedBy a N G)) N G =
LinearCompletion ((bidMaximizedBy a N G) Elsee 0) N G" using lm10 by metis

corollary lm12: "LinearCompletion (maxbid' a N G) N G = LinearCompletion (maxbid a N G) N G"
unfolding maxbid_def using lm11 by metis

lemma lm13: assumes "x \<in> (N \<times> (Pow G - {{}}))" shows 
"linearCompletion' (maxbid' a N G) N G x = linearCompletion (maxbid a N G) N G x"
(is "?f1 ?g1 N G x = ?f2 ?g2 N G x")
using assms lm02 lm12  
proof -
let ?h1="maxbid' a N G" let ?h2="maxbid a N G" let ?hh1="real \<circ> ?h1" let ?hh2="real \<circ> ?h2"
have "LinearCompletion ?h1 N G = LinearCompletion ?h2 N G" using lm12 by metis 
moreover have "linearCompletion ?h2 N G=(LinearCompletion ?h2 N G) Elsee 0"
unfolding linearCompletion_def by fast
ultimately have " linearCompletion ?h2 N G=LinearCompletion ?h1 N G Elsee 0" by presburger
moreover have "... x = (toFunction (LinearCompletion ?h1 N G)) x" using assms 
lm01 UniformTieBreaking.lm64 by (metis (mono_tags))
ultimately have "linearCompletion ?h2 N G x = (toFunction (LinearCompletion ?h1 N G)) x" 
by (metis (lifting, no_types))
thus ?thesis by simp
qed

corollary lm70c: assumes "card N > 0" "distinct G" shows 
"possibleAllocationsRel N (set G) = set (possibleAllocationsAlg N G)"  
using assms Universes.lm70b by metis

lemma lm24: assumes "card A > 0" "card B > 0" shows "card (A \<union> B) > 0" 
using assms card_gt_0_iff finite_Un sup_eq_bot_iff by (metis(no_types))
corollary lm24b: assumes "card A > 0" shows "card ({a} \<union> A) > 0" using assms lm24 
by (metis card_empty card_insert_disjoint empty_iff finite.emptyI lessI)

corollary assumes "card N > 0" "distinct G" shows
"maximalStrictAllocations' N (set G) b = maximalStrictAllocations N G b"
unfolding allStrictAllocations_def
using assms lm70c lm24b by (metis(no_types))

(*
proof - let ?N="{seller}\<union>N" 
have "card ?N > 0" using assms(1) using 
One_nat_def card.insert card_0_eq card_ge_0_finite finite_Un gr0I insert_absorb sup_bot_left sup_eq_bot_iff zero_neq_one
by (metis )
then have "allAllocations ?N (set G) = set (allStrictAllocations ?N G)"
using assms(2) by (rule lm70c)
then show ?thesis by presburger
qed
*)

corollary lm70d: assumes "card N > 0" "distinct G" shows 
"allAllocations N (set G) = set (allStrictAllocations N G)" 
unfolding allStrictAllocations_def
using assms lm70c by blast 

corollary lm70f: assumes "card N > 0" "distinct G" shows 
"winningAllocationsRel N (set G) b = 
(argmax \<circ> setsum) b (set (allStrictAllocations N G))"
unfolding allStrictAllocations_def
using assms lm70c by (metis comp_apply)

corollary lm70g: assumes "card N > 0" "distinct G" shows
"chosenAllocation' N G b r = chosenAllocation N G b r" 
unfolding chosenAllocation_def using assms lm70f allStrictAllocations_def by (metis(no_types)) 
corollary lm13b: assumes "x \<in> (N \<times> (Pow G - {{}}))" shows "tiebids' a N G x = tiebids a N G x" (is "?L=_") 
proof - 
have "?L = linearCompletion' (maxbid' a N G) N G x" by fast moreover have "...= 
linearCompletion (maxbid a N G) N G x" using assms by (rule lm13) ultimately show ?thesis 
unfolding tiebids_def by fast
qed 

lemma lm14: assumes "card N > 0" "distinct G" "a \<subseteq> (N \<times> (Pow (set G) - {{}}))" shows
"setsum (resolvingBid' N G b r) a = setsum (resolvingBid N G b r) a" (is "?L=?R") 
(* (is "?s ?r' a = ?s ?r a") *)
proof - 
let ?c'="chosenAllocation' N G b r" let ?c="chosenAllocation N G b r" let ?r'="resolvingBid' N G b r"
have "?c' = ?c" using assms(1,2) by (rule lm70g) then
have "?r' = tiebids' ?c N (set G)" by presburger
moreover have "\<forall>x \<in> a. tiebids' ?c N (set G) x = tiebids ?c N (set G) x" using assms(3) lm13b by blast
ultimately have "\<forall>x \<in> a. ?r' x = resolvingBid N G b r x" unfolding resolvingBid_def by presburger
thus ?thesis using setsum.cong by simp
qed
lemma lm15: "allAllocations N G \<subseteq> Pow (N \<times> (Pow G - {{}}))" by (metis PowI lm40c subsetI)
corollary lm14b: assumes "card N > 0" "distinct G" "a \<in> allAllocations N (set G)" 
shows "setsum (resolvingBid' N G b r) a = setsum (resolvingBid N G b r) a"
proof -
have "a \<subseteq> N \<times> (Pow (set G) - {{}})" using assms(3) lm15 by blast 
thus ?thesis using assms(1,2) lm14 by blast
qed

corollary lm14c: assumes "finite N" "distinct G" "a \<in> maximalStrictAllocations' N (set G) b" 
shows "setsum (randomBids' N G b r) a = setsum (randomBids N G b r) a"
proof - 
have "card (N\<union>{seller})>0" using assms(1) sup_eq_bot_iff insert_not_empty
by (metis card_gt_0_iff finite.emptyI finite.insertI finite_UnI)
moreover have "distinct G" using assms(2) by simp
moreover have "a \<in> allAllocations (N\<union>{seller}) (set G)" using assms(3) by fastforce
ultimately show ?thesis unfolding randomBids_def by (rule lm14b)
qed

lemma lm16: assumes "\<forall>x\<in>X. f x = g x" shows "argmax f X=argmax g X" 
using assms Argmax.lm02 Collect_cong image_cong 
by (metis(no_types,lifting))

(*MC: without passing theorem lm02 with "using", e and z3 (through sledgehammer) say this theorem is unprovable *)

corollary lm92e: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"1=card (argmax (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b))"
using assms lm92b lm14c 
proof -
have "\<forall> a \<in> maximalStrictAllocations' N (set G) b. 
setsum (randomBids' N G b r) a = setsum (randomBids N G b r) a" using assms(3,1) lm14c by blast
then have "argmax (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b) =
argmax (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b)" using lm16 by blast
moreover have "card ... = 1" using assms by (rule lm92b)
ultimately show ?thesis by presburger
qed
corollary lm70e: assumes "finite N" "distinct G" shows
"maximalStrictAllocations' N (set G) b=maximalStrictAllocations N G b" 
proof -
let ?N="{seller} \<union> N" 
have "card ?N>0" using assms(1) by (metis (full_types) card_gt_0_iff finite_insert insert_is_Un insert_not_empty)
thus ?thesis using assms(2) lm70d by metis
qed
corollary assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"1=card (argmax (setsum (randomBids N G b r)) (maximalStrictAllocations N G b))"
proof - 
have "1=card (argmax (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b))"
using assms by (rule lm92e)
moreover have "maximalStrictAllocations' N (set G) b = maximalStrictAllocations N G b" 
using assms(3,1) by (rule lm70e) ultimately show ?thesis by metis
qed

lemma "maximalStrictAllocations' N (set G) b \<subseteq> Pow (({seller}\<union>N) \<times> (Pow (set G) - {{}}))"
using lm15 UniformTieBreaking.lm03 subset_trans by (metis (no_types))

lemma lm17: "(image converse) (Union X)=Union ((image converse) ` X)" by auto

lemma "possibleAllocationsRel N G =
Union {converse`(injections Y N)| Y. Y \<in> all_partitions G}" 
by auto

lemma "allAllocations N \<Omega> = Union{{a^-1|a. a\<in>injections Y N}|Y. Y\<in>all_partitions \<Omega>}" by auto
term "(\<Sum>i\<in>X. f i)"
term "(\<Union>i\<in>X. x i)"
abbreviation "endowment a n == a,,,n"
abbreviation "vcgEndowment N G b r n==endowment (vcga N G b r) n"

(*abbreviation "f x y == ((x::real)+1)*(y+2)"*)

abbreviation "firstPriceP N \<Omega> b r n ==
b (n, winningAllocationAlg N \<Omega> r b,, n)"

lemma assumes "\<forall> X. b (n, X) \<ge> 0" shows
"firstPriceP N \<Omega> b r n \<ge> 0" using assms by blast

(*
value "injections_alg [0::nat,1] {11::nat, 12}"
thy_deps

theorem counterexample_lm64c: assumes "a \<in> allocationsUniverse" 
"n1\<in> Domain a" "n2 \<in> Domain a"
shows "a,,,n1 \<inter> a,,,n2={}" nitpick
value "vcgaAlg (int`N00) G00 (b00 Elsee 0) 1" 
*)


(* MC: test examples, commented out 
definition "N00 = {1,6::nat}"
definition "G00 = [11::nat, 12, 13]"
definition "b00 = 
{
((1::nat,{11::nat}),3::nat),
((1,{12}),0),
((1,{11,12}),4),
((2,{11}),2),
((2,{12}),2),
((2,{11,12}),1)
}"
term b00
(* definition "example = vcgaAlg (int`N00) G00 (b00 Elsee 0) 1" *)
definition ao where "ao=(%x. (if x=0 then (24::nat) else 11))"

value "randomBids {1,2,3} [11,12,13] (b01 Elsee 0) 1 (2,{12})" 
definition "N01={1::integer,2,3}"
definition "G01=[11::integer,12,13]"
definition "f01=b01 Elsee 0"
definition "evaluateMe01 = vcgaAlg N01 G01 f01 1"
definition "evaluateMe02 = maximalStrictAllocations N01 G01 f01"
definition "evaluateMe03 = randomBids N01 G01 f01 1 (2,{12})"
value "chosenAllocation (N01\<union>{seller}) G01 f01 1" 
definition "chosenAllocation01={(2, {12}), (3, {13, 11})}"
(* value "graph ((N01\<union>{seller}) \<times> (Pow (set G01)-{{}})) (randomBids N01 G01 f01 1)" *) 
abbreviation "graphRandomBids01::((integer \<times> integer set) \<times> nat) set ==
{((3, {12, 13}), 1), ((3, {12}), 0), ((3, {}), 0), ((3, {13}), 1), ((3, {11, 13}), 2), ((3, {11}), 1),
  ((3, {11, 12}), 1), ((3, {11, 12, 13}), 2), ((2, {12, 13}), 1), ((2, {12}), 1), ((2, {}), 0), ((2, {13}), 0),
  ((2, {11, 13}), 0), ((2, {11}), 0), ((2, {11, 12}), 1), ((2, {11, 12, 13}), 1), ((1, {12, 13}), 0),
  ((1, {12}), 0), ((1, {}), 0), ((1, {13}), 0), ((1, {11, 13}), 0), ((1, {11}), 0), ((1, {11, 12}), 0),
  ((1, {11, 12, 13}), 0), ((seller, {12, 13}), 0), ((seller, {12}), 0), ((seller, {}), 0), ((seller, {13}), 0),
  ((seller, {11, 13}), 0), ((seller, {11}), 0), ((seller, {11, 12}), 0), ((seller, {11, 12, 13}), 0)}"
value "graph ((N01\<union>{seller}) \<times> (Pow (set G01)-{{}})) (tiebids 
chosenAllocation01 
N01 (set G01))"
(* 
MC: A key hint is in the much longer evaluation time of the following, compared to the one above
MC: fixed by changing "abbreviation tiebids ..." into "definition tiebids ..."
*)
value "graph ((N01\<union>{seller}) \<times> (Pow (set G01)-{{}})) (tiebids 
(chosenAllocation (N01\<union>{seller}) G01 f01 1) N01 (set G01))"

value "vcgaAlg N01 G01 f01 1"
value "b01 \<union> {}"

*)

abbreviation "goods == sorted_list_of_set o Union o Range o Domain"
(*
abbreviation "b02==b01 \<union> ({1,2,3}\<times>{{14},{15}})\<times>{20}"
abbreviation "N02==participants b02"
abbreviation "G02==goods b02"
abbreviation "f02==b02 Elsee 0"

(*value "chosenAllocation (N02\<union>{seller}) G02 f02 1"
value "maximalStrictAllocations (N02\<union>{seller}) G02 f02"*)
abbreviation "chosenAllocation02==
{(2, {14}), (3, {15}), (1, {12, 13, 11})}" 
value "graph ((N02\<union>{seller}) \<times> (Pow (set G02)-{{}}))
(tiebids chosenAllocation02 (participants b02) (set (goods b02)))"
(*value "graph ((N02\<union>{seller}) \<times> (Pow (set G02)-{{}}))
(tiebids (chosenAllocation (N02\<union>{seller}) G02 f02 1) (participants b02) (set (goods b02)))"*)
(*value "graph ((N02\<union>{seller}) \<times> (Pow (set G02)-{{}}))
(resolvingBid (N02\<union>{seller}) G02 f02 1)"*) 
(* value "randomBids ((fst o fst)`b02) (sorted_list_of_set (Union ((snd o fst)`b02))) (b02 Elsee 0) 1 (1,{11})" *)
*)

(* part to make input/output easier *)
abbreviation "allocationPrettyPrint2 a == map (%x. (x, sorted_list_of_set(a,,x))) ((sorted_list_of_set \<circ> Domain) a)"
definition "helper (list) == (((hd\<circ>hd) list, set (list!1)), hd(list!2))"
definition "listBid2funcBid listBid = (helper`(set listBid)) Elsee (0::integer)"

abbreviation "singleBidConverter x == ((fst x, set ((fst o snd) x)), (snd o snd) x)"
definition "Bid2funcBid b = set (map singleBidConverter b) Elsee (0::integer)"

abbreviation "participantsSet b == fst ` (set b)"
abbreviation "goodsList2 b == sorted_list_of_set (Union ((set o fst o snd) `(set b)))"

definition "allocation b r = {allocationPrettyPrint2 
(vcgaAlg ((participantsSet b)) (goodsList2 b) (Bid2funcBid b) r)
}"

definition "payments b r = vcgpAlg ((participantsSet b)) (goodsList2 b) (Bid2funcBid b) r"
export_code allocation payments in Scala module_name VCG file "/dev/shm/VCG.scala"





abbreviation "b01 == 
{
((1::integer,{11::integer, 12, 13}),20::integer),
((1,{11,12}),18),
((2,{11}),10),
((2,{12}),15),
((2,{12,13}),18),
((3,{11}),2),
((3,{11,12}),12),
((3,{11,13}),17),
((3,{12,13}),18),
((3,{11,12,13}),19),
((4,{11,12,13,14,15,16}),19)
}"
value "participants b01"
(*
MC: Why does this 
value "maximalStrictAllocations {1,2,3} [11, 12, 13]
 (%x. (0::integer))"
take longer than this?
value "maximalStrictAllocations {1,2,3} [11, 12, 13]
 (b01 Elsee 0)"
*)
(* value "possibleAllocationsAlg3 {1,2,3,4,5,6,7,8} [11, 12, 13, 14, 15, 16, 17, 18, 19]"*)

end

(* 
{ { echo asdff; tac ../VCG.scala ; } | sed -n -e '1,/\}/ !p'  | tac | cat - ../addedWrapper.scala; echo \}; }| sed -e "s/\(Nat\)\([^a-zA-Z]\)/NNat\2/g; s/\(Sup_set\)\([^a-zA-Z]\)/SSup_set\2/g"
*)
