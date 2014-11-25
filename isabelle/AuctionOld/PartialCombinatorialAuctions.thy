
theory PartialCombinatorialAuctions

imports
(* Complex *)
UniformTieBreaking
Maximum
(* "../Maskin3"*)
CombinatorialAuction
CombinatorialVickreyAuction            
"~~/src/HOL/Library/Code_Target_Nat"
(*"~~/src/HOL/Library/Permutation"
"~~/src/HOL/Library/Permutations"*)
(*"~~/src/HOL/Library/Indicator_Function"*)
(*"~~/../afp-2014-07-13/thys/List-Infinite/ListInf/List2"*) 
(*"~~/src/HOL/Library/DAList"*)

begin

type_synonym bidvector' = "((participant \<times> goods) \<times> price) set"
abbreviation "Participants b' == Domain (Domain b')"
abbreviation "addedBidder' == (-1::int)"
abbreviation "allStrictAllocations' N G == possibleAllocationsRel N G"
abbreviation "allStrictAllocations'' N \<Omega> == allInjections \<inter> 
{a. Domain a \<subseteq> N & Range a \<in> all_partitions \<Omega>}" 
abbreviation "allStrictAllocations''' N G == allocationsUniverse\<inter>{a. Domain a \<subseteq> N & \<Union> Range a = G}"
lemma nn28: "allStrictAllocations' N G=allStrictAllocations'' N G & 
allStrictAllocations' N G=allStrictAllocations''' N G" using lm19 nn24 by metis
lemma nn28b: "(a \<in> allStrictAllocations''' N G) = (a \<in> allocationsUniverse& Domain a \<subseteq> N & \<Union> Range a = G)"
by force
abbreviation "allAllocations' N \<Omega> == 
(Outside' {addedBidder'}) ` (allStrictAllocations' (N \<union> {addedBidder'}) \<Omega>)"
abbreviation "allAllocations'' N \<Omega> == 
(Outside' {addedBidder'}) ` (allStrictAllocations'' (N \<union> {addedBidder'}) \<Omega>)"
abbreviation "allAllocations''' N \<Omega> == 
(Outside' {addedBidder'}) ` (allStrictAllocations''' (N \<union> {addedBidder'}) \<Omega>)"
lemma nn28c: 
"allAllocations' N G = allAllocations'' N G & allAllocations'' N G = allAllocations''' N G"
using assms nn28 by metis
corollary nn28d: "allAllocations' = allAllocations'' & allAllocations'' = allAllocations'''
& allAllocations' = allAllocations'''" using nn28c by metis
lemma nn32: "allAllocations' (N-{addedBidder'}) G \<subseteq> allAllocations' N G" using Outside_def by simp

lemma nn34: "(a \<in> allocationsUniverse) = (a \<in> allStrictAllocations''' (Domain a) (\<Union> Range a))"
by blast
lemma nn35: assumes "N1 \<subseteq> N2" shows "allStrictAllocations''' N1 G \<subseteq> allStrictAllocations''' N2 G" 
using assms by auto
lemma nn36: assumes "a \<in> allStrictAllocations''' N G" shows "Domain (a -- x) \<subseteq> N-{x}" 
using assms Outside_def by fastforce
lemma nn37: assumes "a \<in> allAllocations' N G" shows "a \<in> allocationsUniverse"
using assms lm35 Outside_def image_iff nn24c by smt
lemma nn38: assumes "a \<in> allAllocations' N G" shows "a \<in> allStrictAllocations''' (Domain a) (\<Union>Range a)"
proof - show ?thesis using assms nn37 by blast qed
lemma  assumes "N1 \<subseteq> N2" shows "allAllocations''' N1 G \<subseteq> allAllocations''' N2 G"
using assms nn35 nn36 nn37 nn24c nn28b nn28 nn34 nn38 Outside_def by blast
lemma nn39a: "{} \<in> allInjections" by (metis converse_empty mem_Collect_eq runiq_emptyrel)
lemma nn39b: "{} \<in> allPartitionvalued" by (metis (lifting) Pow_bottom UN_iff lm36b)
(* corollary nn39: "{} \<in> allocationsUniverse using nn39a nn39b by blast*)
lemma lll59b: "runiq (X\<times>{y})" using lll59 by (metis trivial_singleton)
lemma lm37b: "{x}\<times>{y} \<in> allInjections" using lm37 by fastforce
lemma nn40b: assumes "a \<in> allAllocations''' N G" shows "\<Union> Range a \<subseteq> G" using assms Outside_def by blast
lemma nn41: "a \<in> allAllocations''' N G = 
(EX aa. aa -- (addedBidder')=a & aa\<in>allStrictAllocations''' (N \<union> {addedBidder'}) G)" by blast

lemma nn37e: assumes "a \<in> allocationsUniverse" "Domain a \<subseteq> N-{addedBidder'}" "\<Union> Range a \<subseteq> G" shows
"a \<in> allAllocations''' N G" using assms nn41 
proof -
let ?i="addedBidder'" let ?Y="{G-\<Union> Range a}-{{}}" let ?b="{?i}\<times>?Y" let ?aa="a\<union>?b"
let ?aa'="a +* ?b" 
have
1: "a \<in> allocationsUniverse" using assms(1) by fast 
have "?b \<subseteq> {(?i,G-\<Union> Range a)} - {(?i, {})}" by fastforce then have 
2: "?b \<in> allocationsUniverse" using lm38 by (smt lm35b) have 
3: "\<Union> Range a \<inter> \<Union> (Range ?b) = {}" by blast have 
4: "Domain a \<inter> Domain ?b ={}" using assms by fast
have "?aa \<in> allocationsUniverse" using 1 2 3 4 by (rule lm23)
then have "?aa \<in> allStrictAllocations''' (Domain ?aa) 
(\<Union> Range ?aa)" unfolding nn34 by metis then have 
"?aa \<in> allStrictAllocations''' (N\<union>{?i}) (\<Union> Range ?aa)" using nn35 assms paste_def by auto
moreover have "Range ?aa = Range a \<union> ?Y" by blast then moreover have 
"\<Union> Range ?aa = G" using Un_Diff_cancel Un_Diff_cancel2 Union_Un_distrib Union_empty Union_insert  
by (metis (lifting, no_types) assms(3) cSup_singleton subset_Un_eq) moreover have 
"?aa' = ?aa" using 4 by (rule paste_disj_domains)
ultimately have "?aa' \<in> allStrictAllocations''' (N\<union>{?i}) G" by simp
moreover have "Domain ?b \<subseteq> {?i}" by fast then moreover have "?aa' -- ?i = a -- ?i" using ll19 
by (smt Un_empty_right empty_subsetI insert_subset subset_Un_eq subset_antisym subset_insert)
moreover have "... = a" using Outside_def assms(2) by auto 
ultimately show ?thesis using nn41 by auto
qed

lemma nn23: 
"a\<in>allStrictAllocations' N \<Omega>=(a\<in>allInjections & Domain a\<subseteq>N & Range a\<in>all_partitions \<Omega>)" 
by (metis (full_types) lm19c)

lemma nn37b: assumes "a \<in> allAllocations''' N G" shows "Domain a \<subseteq> N-{addedBidder'} & a \<in> allocationsUniverse"  
proof -
let ?i="addedBidder'" obtain aa where
0: "a=aa -- ?i & aa \<in> allStrictAllocations''' (N \<union> {?i}) G" using assms(1) nn41 by blast
then have "Domain aa \<subseteq> N \<union> {?i}" using nn23 by blast
then have "Domain a \<subseteq> N - {?i}" using 0 Outside_def by blast
moreover have "a \<in> allAllocations' N G" using assms nn28d by metis
then moreover have "a \<in> allocationsUniverse" using nn37 by blast
ultimately show ?thesis by blast
qed

corollary nn37c: assumes "a \<in> allAllocations''' N G" shows 
"a \<in> allocationsUniverse & Domain a \<subseteq> N-{addedBidder'} & \<Union> Range a \<subseteq> G"
proof -
have "a \<in> allocationsUniverse" using assms nn37b by blast
moreover have "Domain a \<subseteq> N-{addedBidder'}" using assms nn37b by blast
moreover have "\<Union> Range a \<subseteq> G" using assms nn40b by blast
ultimately show ?thesis by blast
qed

corollary nn37d: 
"(a\<in>allAllocations''' N G)=(a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder'} & \<Union> Range a \<subseteq> G)" 
using nn37c nn37e by (metis (mono_tags))

lemma nn42: "(a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder'} & \<Union> Range a \<subseteq> G) = 
(a\<in>allocationsUniverse& a\<in>{aa. Domain aa \<subseteq> N-{addedBidder'} & \<Union> Range aa \<subseteq> G})" 
by (metis (lifting, no_types) mem_Collect_eq)

corollary nn37f: "(a\<in>allAllocations''' N G)=
(a\<in>allocationsUniverse& a\<in>{aa. Domain aa \<subseteq> N-{addedBidder'} & \<Union> Range aa \<subseteq> G})" (is "?L = ?R") 
proof -
  have "?L = (a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder'} & \<Union> Range a \<subseteq> G)" by (rule nn37d)
  moreover have "... = ?R" by (rule nn42) ultimately show ?thesis by presburger
qed

corollary nn37g: "a\<in>allAllocations''' N G=
(a\<in> (allocationsUniverse \<inter> {aa. Domain aa \<subseteq> N-{addedBidder'} & \<Union> Range aa \<subseteq> G}))" 
using nn37f by (metis (mono_tags) Int_iff)

abbreviation "allAllocations'''' N G == 
allocationsUniverse\<inter>{aa. Domain aa\<subseteq>N-{addedBidder'} & \<Union>Range aa\<subseteq>G}"

theorem nn44: assumes "a \<in> allAllocations'''' N G" shows "a -- n \<in> allAllocations'''' (N-{n}) G"
proof -
  let ?bb=addedBidder' let ?d=Domain let ?r=Range let ?X2="{aa. ?d aa\<subseteq>N-{?bb} & \<Union>?r aa\<subseteq>G}" 
  let ?X1="{aa. ?d aa\<subseteq>N-{n}-{?bb} & \<Union>?r aa\<subseteq>G}" 
  have "a\<in>?X2" using assms(1) by fast then have 
  0: "?d a \<subseteq> N-{?bb} & \<Union>?r a \<subseteq> G" by blast then have "?d (a--n) \<subseteq> N-{?bb}-{n}" 
  using outside_reduces_domain by (metis Diff_mono subset_refl) moreover have 
  "... = N-{n}-{?bb}" by fastforce ultimately have 
  "?d (a--n) \<subseteq> N-{n}-{?bb}" by blast moreover have "\<Union> ?r (a--n) \<subseteq> G" 
  unfolding Outside_def using 0 by blast ultimately have "a -- n \<in> ?X1" by fast moreover have 
  "a--n \<in> allocationsUniverse" using assms by (smt Int_iff lm35d) ultimately show ?thesis by blast
qed

corollary nn37h: "allAllocations''' N G=allAllocations'''' N G"
(is "?L=?R") proof - {fix a have "a \<in> ?L = (a \<in> ?R)" by (rule nn37g)} thus ?thesis by blast qed

theorem nn28e: "allAllocations'=allAllocations'' & allAllocations''=allAllocations''' &
allAllocations'''=allAllocations''''" using nn37h nn28d by metis

theorem nn44b: assumes "a \<in> allAllocations' N G" shows "a -- n \<in> allAllocations' (N-{n}) G"
(* MC: being an allocation is invariant to subtracting any single bidder 
This is the fundamental step to prove non-negativity of vcgp' *)
proof - 
let ?A'=allAllocations'''' have "a \<in> ?A' N G" using assms nn28e by metis then
have "a -- n \<in> ?A' (N-{n}) G" by (rule nn44) thus ?thesis using nn28e by metis 
qed

corollary nn37i: assumes "G1 \<subseteq> G2" shows "allAllocations'''' N G1 \<subseteq> allAllocations'''' N G2"
using assms by blast

corollary nn33: assumes "G1 \<subseteq> G2" shows "allAllocations''' N G1 \<subseteq> allAllocations''' N G2"
using assms nn37i nn37h 
proof -
have "allAllocations''' N G1 = allAllocations'''' N G1" by (rule nn37h)
moreover have "... \<subseteq> allAllocations'''' N G2" using assms(1) by (rule nn37i)
moreover have "... = allAllocations''' N G2" using nn37h by metis
ultimately show ?thesis by auto
qed

abbreviation "maximalAllocations'' N \<Omega> b == arg_max' (setsum b) (allAllocations' N \<Omega>)"

abbreviation "maximalStrictAllocations' N G b==
arg_max' (setsum b) (allStrictAllocations' ({addedBidder'}\<union>N) G)"
(*MC: these are the allocations maximizing the revenue, and also including the unallocated goods assigned to
the virtual participant addedBidder. 
Note that commonly b is set to zero identically for such bidder, but this is not formally imposed here.*)
(*abbreviation "allAllocations N G == possibleAllocationsAlg3 N G"
abbreviation "maximalAllocations G b == argmax (setsum' b) ((allAllocations (Participants b) G))"
*)

corollary lm43d: assumes "a \<in> allocationsUniverse" shows 
"(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> allocationsUniverse" using assms lm43b 
by fastforce

lemma nn27c: "addedBidder' \<notin> int `N" by fastforce

abbreviation "randomBids' N \<Omega> b random==resolvingBid' (N\<union>{addedBidder'}) \<Omega> b random"

theorem mm92b: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"card (arg_max' (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b))=1"
(*MC: Here we are showing that our way of randomizing using randomBids' actually breaks the tie:
we are left with a singleton after the tiebreaking round*)
(is "card ?L=_") proof -
let ?n="{addedBidder'}" have 
1: "(?n \<union> N)\<noteq>{}" by simp have 
4: "finite (?n\<union>N)" using assms(3) by fast have 
"terminatingAuctionRel (?n\<union>N) G b r = {chosenAllocation' (?n\<union>N) G b r}" using 1 assms(1) 
assms(2) 4 by (rule mm92) moreover have "?L = terminatingAuctionRel (?n\<union>N) G b r" by auto
ultimately show ?thesis by auto
qed

lemma "arg_max' (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b) \<subseteq> 
maximalStrictAllocations' N (set G) b" by auto

abbreviation "vcga' N G b r == (the_elem
(arg_max' (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b))) -- addedBidder'"

corollary nn58: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"the_elem
(arg_max' (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b)) \<in>
(maximalStrictAllocations' N (set G) b)" (is "the_elem ?X \<in> ?R") using assms mm92b nn57
proof -
have "card ?X=1" using assms by (rule mm92b) moreover have "?X \<subseteq> ?R" by auto
ultimately show ?thesis using nn57b by blast
qed

corollary nn58b: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga' N G b r \<in> (Outside' {addedBidder'})`(maximalStrictAllocations' N (set G) b)"
using assms nn58 by blast

lemma nn62: "(Outside' {addedBidder'})`(maximalStrictAllocations' N G b) \<subseteq> allAllocations' N G"
using Outside_def by force

theorem nn58d: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga' N G b r \<in> allAllocations' N (set G)" (is "?a \<in> ?A") using assms nn58b nn62 
proof - have "?a \<in> (Outside' {addedBidder'})`(maximalStrictAllocations' N (set G) b)" 
using assms by (rule nn58b) thus ?thesis using nn62  by fastforce qed

corollary nn59b: assumes "\<forall>X. X \<in> Range a \<longrightarrow>b (addedBidder', X)=0" "finite a" shows 
"setsum b a = setsum b (a--addedBidder')"
proof -
let ?n=addedBidder' have "finite (a||{?n})" using assms restrict_def by (metis finite_Int) 
moreover have "\<forall>z \<in> a||{?n}. b z=0" using assms restrict_def by fastforce
ultimately have "setsum b (a||{?n}) = 0" using assms restrict_def by (metis setsum.neutral)
thus ?thesis using nn59 assms(2) by (metis comm_monoid_add_class.add.right_neutral)
qed

corollary nn59c: assumes "\<forall>a\<in>A. finite a & (\<forall> X. X\<in>Range a \<longrightarrow> b (addedBidder', X)=0)"
shows "{setsum b a| a. a\<in>A}={setsum b (a -- addedBidder')| a. a\<in>A}" using assms nn59b 
by (metis (lifting, no_types) Collect_cong)
corollary nn58c: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"EX a. ((a \<in> (maximalStrictAllocations' N (set G) b)) 
& (vcga' N G b r = a -- addedBidder') 
& (a \<in> arg_max' (setsum b) (allStrictAllocations' ({addedBidder'}\<union>N) (set G)))
)" (is "EX a. _ & _ & a \<in> ?X")
using assms nn58b arg_max'_def by fast

lemma assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"\<forall>aa\<in>allStrictAllocations' ({addedBidder'}\<union>N) (set G). finite aa"
using assms by (metis List.finite_set mm44)

theorem nn61: assumes "distinct G" "set G \<noteq> {}" "finite N" 
"\<forall>aa\<in>allStrictAllocations' ({addedBidder'}\<union>N) (set G). \<forall> X \<in> Range aa. b (addedBidder', X)=0"
(is "\<forall>aa\<in>?X. _") shows "setsum b (vcga' N G b r)=Max{setsum b aa| aa. aa \<in> allAllocations' N (set G)}"
(*MC: adequacy theorem *)
proof -
let ?n=addedBidder' let ?s=setsum let ?a="vcga' N G b r" obtain a where 
0: "a \<in> maximalStrictAllocations' N (set G) b & ?a=a--?n & 
(a\<in>arg_max' (setsum b) (allStrictAllocations'({addedBidder'}\<union>N)(set G)))"(is "_ & ?a=_ & a\<in>?Z")
using assms(1,2,3) nn58c by blast have 
1: "\<forall>aa\<in>?X. finite aa & (\<forall> X. X\<in>Range aa \<longrightarrow> b (?n, X)=0)" using assms(4) 
List.finite_set mm44 by metis have 
2: "a \<in> ?X" using 0 by auto have "a \<in> ?Z" using 0 by fast 
then have "a \<in> ?X\<inter>{x. ?s b x = Max (?s b ` ?X)}" using mm78 by simp
then have "?s b a = Max {?s b aa| aa. aa\<in>?X}" using Collect_cong Int_iff image_Collect_mem mem_Collect_eq by smt
moreover have "{?s b aa| aa. aa\<in>?X} = {?s b (aa--?n)| aa. aa\<in>?X}" using 1 by (rule nn59c)
moreover have "... = {?s b aa| aa. aa \<in> Outside' {?n}`?X}" by blast
moreover have "... = {?s b aa| aa. aa \<in> allAllocations' N (set G)}" by simp
ultimately have "Max {?s b aa| aa. aa \<in> allAllocations' N (set G)} = ?s b a" by presburger
moreover have "... = ?s b (a--?n)" using 1 2 nn59b by (metis (lifting, no_types))
ultimately show "?s b ?a=Max{?s b aa| aa. aa \<in> allAllocations' N (set G)}" using 0 by presburger
qed

























































corollary nn61b: assumes "distinct G" "set G \<noteq> {}" "finite N" "\<forall> X. b (addedBidder', X)=0" 
shows "setsum b (vcga' N G b r)=Max{setsum b aa| aa. aa \<in> allAllocations' N (set G)}"
using assms nn61 by blast

corollary nn58e: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"vcga' N G b r \<in> allocationsUniverse & \<Union> Range (vcga' N G b r) \<subseteq> set G" using assms nn58b 
proof -
let ?a="vcga' N G b r" let ?n=addedBidder'
obtain a where 
0: "?a=a -- addedBidder' & a \<in> maximalStrictAllocations' N (set G) b"
using assms nn58b by blast
then moreover have 
1: "a \<in> allStrictAllocations' ({?n}\<union>N) (set G)" by auto
moreover have "maximalStrictAllocations' N (set G) b \<subseteq> allocationsUniverse" 
by (metis (lifting, mono_tags) lm03 lm50 subset_trans)
ultimately moreover have "?a=a -- addedBidder' & a \<in> allocationsUniverse" by blast
then have "?a \<in> allocationsUniverse" using lm35d by auto
moreover have "\<Union> Range a= set G" using nn24d 1 by metis
then moreover have "\<Union> Range ?a \<subseteq> set G" using Outside_def 0 by fast
ultimately show ?thesis using lm35d Outside_def by blast
qed

lemma "vcga' N G b r = the_elem ((arg_max' \<circ> setsum) (randomBids' N G b r) 
((arg_max' \<circ> setsum) b (allStrictAllocations' ({addedBidder'}\<union>N) (set G)))) -- addedBidder'" by simp

abbreviation "vcgp' N G b r n ==
(Max (setsum b ` (allAllocations' (N-{n}) (set G)))) - (setsum b (vcga' N G b r -- n))"

lemma nn63: assumes "x \<in> X" "finite X" shows "Max (f`X) >= f x" (is "?L >= ?R") using assms 
by (metis (hide_lams, no_types) Max.coboundedI finite_imageI image_eqI)

theorem NonnegPrices: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcgp' N G (b) r n >= (0::price)" 
proof - 
let ?a="vcga' N G b r" let ?A=allAllocations' let ?A'=allAllocations'''' let ?f="setsum b" 
have "?a \<in> ?A N (set G)" using assms by (rule nn58d)
then have "?a \<in> ?A' N (set G)" using nn28e by metis then have "?a -- n \<in> ?A' (N-{n}) (set G)" by (rule nn44) 
then have "?a -- n \<in> ?A (N-{n}) (set G)" using nn28e by metis
moreover have "finite (?A (N-{n}) (set G))" 
by (metis List.finite_set assms(3) finite.emptyI finite_Diff finite_Un finite_imageI finite_insert lm59) 
ultimately have "Max (?f`(?A (N-{n}) (set G))) >= ?f (?a -- n)" (is "?L >= ?R") by (rule nn63)
then have "?L - ?R >=0" by linarith thus ?thesis by fast
qed

lemma lm19b: "allStrictAllocations' N G = possibleAllocationsRel N G" using assms by (metis lm19)
abbreviation "strictAllocationsUniverse == allocationsUniverse"

abbreviation "Goods bids == \<Union>((snd\<circ>fst)`bids)"

corollary nn45: assumes "a \<in> allAllocations'''' N G" shows "Range a \<in> allPartitions" using assms 
Outside_def 
by (metis (lifting, mono_tags) Int_iff lm22 mem_Collect_eq)

corollary nn45a: assumes "a \<in> allAllocations' N G" shows "Range a \<in> allPartitions"
proof - have "a \<in> allAllocations'''' N G" using assms nn28e by metis thus ?thesis by (rule nn45) qed

corollary assumes 
"N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" (*MC: why does this emerge only now? *) 
shows "(Outside' {addedBidder'}) ` (terminatingAuctionRel N G (bids) random) = 
{chosenAllocation' N G bids random -- (addedBidder')}" (is "?L=?R") using assms mm92 Outside_def 
proof -
have "?R = Outside' {addedBidder'} ` {chosenAllocation' N G bids random}" using Outside_def 
by blast 
moreover have "... = (Outside'{addedBidder'})`(terminatingAuctionRel N G bids random)" using assms mm92 
by blast
ultimately show ?thesis by presburger
qed

abbreviation "argMax X f == arg_max' f X"
lemma "terminatingAuctionRel N G b r = 
((arg_max' (setsum (resolvingBid' N G b (nat r)))) \<circ> (arg_max' (setsum b)))
(possibleAllocationsRel N (set G))" by force
term "(Union \<circ> (arg_max' (setsum (resolvingBid' N G b (nat r)))) \<circ> (arg_max' (setsum b)))
(possibleAllocationsRel N (set G))"

lemma "maximalStrictAllocations' N G b=winningAllocationsRel ({addedBidder'} \<union> N) G b" by fast

lemma nn64: assumes "a \<in> allocationsUniverse" 
"n1 \<in> Domain a" "n2 \<in> Domain a"
"n1 \<noteq> n2" 
shows "a,,n1 \<inter> a,,n2={}" using assms is_partition_def lm22 mem_Collect_eq 
proof - have "Range a \<in> allPartitions" using assms lm22 by blast
moreover have "a \<in> allInjections & a \<in> allPartitionvalued" using assms by (metis (lifting, no_types) IntD1 IntD2)
ultimately moreover have "a,,n1 \<in> Range a" using assms 
by (metis (mono_tags) eval_runiq_in_Range mem_Collect_eq)
ultimately moreover have "a,,n1 \<noteq> a,,n2" using assms 
by (metis (lifting, no_types) converse.intros eval_runiq_rel mem_Collect_eq runiq_imp_uniq_right_comp)
ultimately show ?thesis using is_partition_def by (metis (lifting, no_types) assms(3) eval_runiq_in_Range mem_Collect_eq)
qed

lemma nn64c: assumes "a \<in> allocationsUniverse" 
"n1 \<in> Domain a" "n2 \<in> Domain a"
"n1 \<noteq> n2" 
shows "a,,,n1 \<inter> a,,,n2={}" using assms nn64 lll82 by fastforce 

theorem nn64b:
assumes "distinct G" "set G \<noteq> {}" "finite N"  
"n1 \<in> Domain (vcga' N G b r)" "n2 \<in> Domain (vcga' N G b r)" "n1 \<noteq> n2" 
shows "(vcga' N G b r),,,n1 \<inter> (vcga' N G b r),,,n2={}"  
proof -
have "vcga' N G b r \<in> allocationsUniverse" using nn58e assms by blast
thus ?thesis using nn64c assms by fast
qed

lemma assumes "R,,,x \<noteq> {}" shows "x \<in> Domain R" using assms  
proof - have "\<Union> (R``{x}) \<noteq> {}" using assms(1) by fast
then have "R``{x} \<noteq> {}" by fast thus ?thesis by blast qed

lemma assumes "runiq f" and "x \<in> Domain f" shows "(f ,, x) \<in> Range f" using assms 
by (rule eval_runiq_in_Range)

theorem assumes "distinct G" "set G \<noteq> {}" "finite N" "g \<in> (vcga' N G b r),,,n" 
shows "g \<in> set G" 
proof - 
let ?a="vcga' N G b r" 
have "?a \<in> allocationsUniverse" using assms(1,2,3) nn58e by blast
then have "runiq ?a" using assms(1,2,3) by blast
moreover have "n \<in> Domain ?a" using assms(4) eval_rel_def by fast
ultimately moreover have "?a,,n \<in> Range ?a" using eval_runiq_in_Range by fast 
ultimately have "?a,,,n \<in> Range ?a" using lll82 by fastforce
then have "g \<in> \<Union> Range ?a" using assms by blast 
moreover have "\<Union> Range ?a \<subseteq> set G" using assms(1,2,3) nn58e by fast
ultimately show ?thesis by blast
qed

theorem 
(* assumes 
"distinct G" "set G \<noteq> {}" "finite N"  
"n1 \<in> Domain (vcga' N G b r)" 
"n2 \<in> Domain (vcga' N G b r)" 
"n1 = n2" *)
shows "(vcga' N G b r),,n1 \<inter> (vcga' N G b r),,n2={}" using assms 
sorry

theorem counterexample_nn64c: assumes "a \<in> allocationsUniverse" 
"n1\<in> Domain a" "n2 \<in> Domain a"
shows "a,,,n1 \<inter> a,,,n2={}" sorry

abbreviation "allStrictAllocations N G == possibleAllocationsAlg3 N G"
abbreviation "maximalStrictAllocations N G b==
arg_max' (setsum b) (set (allStrictAllocations ({addedBidder'}\<union>N) G))"

abbreviation "N00 == {1,2::nat}"
abbreviation "G00 == [11::nat, 12, 13]"
abbreviation "A00 == {(0,{10,11::nat}), (1,{12,13})}"
abbreviation "b00 == 
{
((1::int,{11}),3),
((1,{12}),0),
((1,{11,12::nat}),4::price),
((2,{11}),2),
((2,{12}),2),
((2,{11,12}),1)
}"

abbreviation "chosenAllocation N G b r == 
hd(perm2 (takeAll (%x. x\<in> (arg_max' \<circ> setsum) b (set (allStrictAllocations N G))) (allStrictAllocations N G)) r)"

abbreviation "puppa R fallback == (% x. if (x \<in> Domain R) then (R,,x) else fallback)"
notation puppa (infix "Elsee" 75) (* MC: This is computable, `Else' is not *)
abbreviation "maxbid a N G == (bidMaximizedBy a N G) Elsee 0"
abbreviation "linearCompletion (bids) N G == 
 (LinearCompletion bids N G) Elsee 0"
abbreviation "tiebids a N G == linearCompletion (maxbid a N G) N G"
abbreviation "resolvingBid N G bids random == tiebids (chosenAllocation N G bids random) N (set G)"
abbreviation "randomBids N \<Omega> b random==resolvingBid (N\<union>{addedBidder'}) \<Omega> b random"
abbreviation "vcga N G b r == (the_elem
(arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations N G b))) -- addedBidder'"

lemma lm01: assumes "x \<in> Domain f" shows "toFunction f x = (f Elsee 0) x" 
by (metis assms toFunction_def)

lemma lm02: assumes "x \<in> (N \<times> (Pow G - {{}}))" shows 
"linearCompletion' b N G x=linearCompletion b N G x"
using assms lm01 mm64 by (smt Domain.simps imageI)

lemma lm03: "Domain (Y \<times> {0::nat}) = Y & Domain (X \<times> {1})=X" by blast
lemma lm04: "Domain (X <|| Y) = X \<union> Y" using lm03 paste_Domain sup_commute by metis
corollary 05: "Domain (bidMaximizedBy a N G) = pseudoAllocation a \<union> N \<times> (finestpart G)" using lm04 
by metis

lemma assumes "a \<in> possibleAllocationsRel N G" shows "pseudoAllocation a \<subseteq> Domain (bidMaximizedBy a N G)" 
using assms sorry

corollary assumes 
"pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" "finite (pseudoAllocation aa)"
shows "setsum ((bidMaximizedBy a N G) Elsee 0) (pseudoAllocation a) - 
(setsum ((bidMaximizedBy a N G) Elsee 0) (pseudoAllocation aa)) = 
card (pseudoAllocation a) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" 
(is "?l1 - ?l2 = ?r") using mm28 assms mm49 lm04 lm05 Un_upper1 UnCI UnI1 
proof -
have "?l1 = setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation a)"
using assms lm01 setsum_cong2 by (smt lm04 UnI1) 
moreover have "?l2 = setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation aa)"
using assms lm01 setsum_cong2 UnI1 lm04 by (smt in_mono)
ultimately have "?l1 - ?l2 = setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation a) 
- setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation aa)" by presburger
moreover have "... = ?r" using assms mm49 mm28 by fast
ultimately show ?thesis by presburger
qed

lemma lm06: assumes "fst pair \<in> N" "snd pair \<in> Pow G - {{}}" shows "setsum (%g.
(toFunction (bidMaximizedBy a N G))
(fst pair, g)) (finestpart (snd pair)) =
setsum (%g. 
((bidMaximizedBy a N G) Elsee 0)
(fst pair, g)) (finestpart (snd pair))"
using assms lm01 lm05 lm04 Un_upper1 UnCI UnI1 setsum_cong2 mm55n Diff_iff Pow_iff in_mono
proof -
let ?f1="%g.(toFunction (bidMaximizedBy a N G))(fst pair, g)"
let ?f2="%g.((bidMaximizedBy a N G) Elsee 0)(fst pair, g)"
{ 
  fix g assume "g \<in> finestpart (snd pair)" then have "g \<in> finestpart G" using assms mm55n 
  by (metis Diff_iff Pow_iff in_mono)
  then have "?f1 g = ?f2 g" using assms lm01 lm04 lm05 by (smt SigmaI UnI2)
}
thus ?thesis using setsum_cong2 by simp
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
using lm11 by metis

(*value "vcga (int`N00) G00 (b00 Elsee 0) 1"*)

lemma lm13: assumes "x \<in> (N \<times> (Pow G - {{}}))" shows 
"linearCompletion' (maxbid' a N G) N G x = linearCompletion (maxbid a N G) N G x"
(is "?f1 ?g1 N G x = ?f2 ?g2 N G x")
using assms lm02 lm12  
proof -
let ?h1="maxbid' a N G" let ?h2="maxbid a N G" let ?hh1="real \<circ> ?h1" let ?hh2="real \<circ> ?h2"
have "LinearCompletion ?h1 N G = LinearCompletion ?h2 N G" using lm12 by metis 
moreover have "linearCompletion ?h2 N G=(LinearCompletion ?h2 N G) Elsee 0" by fast
ultimately have " linearCompletion ?h2 N G=LinearCompletion ?h1 N G Elsee 0" by presburger
moreover have "... x = (toFunction (LinearCompletion ?h1 N G)) x" using assms by (metis (mono_tags) lm01 mm64)
ultimately have "linearCompletion ?h2 N G x = (toFunction (LinearCompletion ?h1 N G)) x" 
by (metis (lifting, no_types))
thus ?thesis by simp
qed

corollary lm70c: assumes "card N > 0" "distinct G" shows 
"possibleAllocationsRel N (set G) = set (possibleAllocationsAlg3 N G)"  
using assms lm70b 01 by metis

corollary lm70d: assumes "card N > 0" "distinct G" shows 
"allStrictAllocations' N (set G) = set (allStrictAllocations N G)" using assms lm70c by blast 

corollary lm70f: assumes "card N > 0" "distinct G" shows 
"winningAllocationsRel N (set G) b = 
(arg_max' \<circ> setsum) b (set (allStrictAllocations N G))" using assms lm70c by (metis comp_apply)

corollary lm70g: assumes "card N > 0" "distinct G" shows
"chosenAllocation' N G b r = chosenAllocation N G b r" using assms lm70f by metis 
corollary lm13b: assumes "x \<in> (N \<times> (Pow G - {{}}))" shows "tiebids' a N G x = tiebids a N G x" (is "?L=_") 
proof - 
have "?L = linearCompletion' (maxbid' a N G) N G x" by fast moreover have "...= 
linearCompletion (maxbid a N G) N G x" using assms by (rule lm13) ultimately show ?thesis by fast
qed 

lemma lm14: assumes "card N > 0" "distinct G" "a \<subseteq> (N \<times> (Pow (set G) - {{}}))" shows
"setsum (resolvingBid' N G b r) a = setsum (resolvingBid N G b r) a" (is "?L=?R") 
(* (is "?s ?r' a = ?s ?r a") *)
proof - 
let ?c'="chosenAllocation' N G b r" let ?c="chosenAllocation N G b r" let ?r'="resolvingBid' N G b r"
have "?c' = ?c" using assms(1,2) by (rule lm70g) then
have "?r' = tiebids' ?c N (set G)" by presburger
moreover have "\<forall>x \<in> a. tiebids' ?c N (set G) x = tiebids ?c N (set G) x" using assms(3) lm13b by blast
ultimately have "\<forall>x \<in> a. ?r' x = resolvingBid N G b r x" by presburger
thus ?thesis using setsum_cong2 by simp
qed
lemma lm15: "allStrictAllocations' N G \<subseteq> Pow (N \<times> (Pow G - {{}}))" by (metis PowI mm63c subsetI)
corollary lm14b: assumes "card N > 0" "distinct G" "a \<in> allStrictAllocations' N (set G)" 
shows "setsum (resolvingBid' N G b r) a = setsum (resolvingBid N G b r) a"
proof - 
have "a \<subseteq> N \<times> (Pow (set G) - {{}})" using assms(3) lm15 by blast 
thus ?thesis using assms(1,2) lm14 by blast
qed

corollary lm14c: assumes "finite N" "distinct G" "a \<in> maximalStrictAllocations' N (set G) b" 
shows "setsum (randomBids' N G b r) a = setsum (randomBids N G b r) a"
proof - 
have "card (N\<union>{addedBidder'})>0" using assms(1) sup_eq_bot_iff insert_not_empty
by (metis card_gt_0_iff finite.emptyI finite.insertI finite_UnI)
moreover have "distinct G" using assms(2) by simp
moreover have "a \<in> allStrictAllocations' (N\<union>{addedBidder'}) (set G)" using assms(3) by fastforce
ultimately show ?thesis by (rule lm14b)
qed

lemma lm16: assumes "\<forall>x\<in>X. f x = g x" shows "arg_max' f X=arg_max' g X" 
using assms Misc1.lm02 by (smt Collect_cong image_cong) 
(*MC: without passing theorem Misc1.lm02 with "using", e and z3 (through sledgehammer) say this theorem is unprovable *)

corollary mm92c: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"1=card (arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b))"
using assms mm92b lm14c 
proof -
have "\<forall> a \<in> maximalStrictAllocations' N (set G) b. 
setsum (randomBids' N G b r) a = setsum (randomBids N G b r) a" using assms(3,1) lm14c by blast
then have "arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b) =
arg_max' (setsum (randomBids' N G b r)) (maximalStrictAllocations' N (set G) b)" using lm16 by blast
moreover have "card ... = 1" using assms by (rule mm92b)
ultimately show ?thesis by presburger
qed
corollary lm70e: assumes "finite N" "distinct G" shows
"maximalStrictAllocations' N (set G) b=maximalStrictAllocations N G b" 
proof -
let ?N="{addedBidder'} \<union> N" 
have "card ?N>0" using assms(1) by (metis (full_types) card_gt_0_iff finite_insert insert_is_Un insert_not_empty)
thus ?thesis using assms(2) lm70d by metis
qed
corollary assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"1=card (arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations N G b))"
proof - 
have "1=card (arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b))"
using assms by (rule mm92c)
moreover have "maximalStrictAllocations' N (set G) b = maximalStrictAllocations N G b" 
using assms(3,1) by (rule lm70e) ultimately show ?thesis by metis
qed

lemma "maximalStrictAllocations' N (set G) b \<subseteq> Pow (({addedBidder'}\<union>N) \<times> (Pow (set G) - {{}}))"
using PowI mm63c subsetI by (smt Misc2.lm03 Sigma_cong set_rev_mp)
























































corollary "LinearCompletion (bidMaximizedBy a N G Elsee 0) N G =
LinearCompletion (toFunction (bidMaximizedBy a N G)) N G" using lm07 image_cong lm08 
sorry

corollary lm02b: 
assumes "x \<in> (N \<times> (Pow G - {{}}))" shows 
"tiebids a N G x=linearCompletion' b N G x"

term vcga'
term vcgp'


lemma "arg_max' (setsum (resolvingBid' N G bids random)) (arg_max' (setsum bids) (possibleAllocationsRel N (set G)))
=
arg_max' (setsum (resolvingBid N G bids random)) (arg_max' (setsum bids) (possibleAllocationsRel N (set G)))"
using assms sorry


theorem
assumes "distinct G" "set G \<noteq> {}" "finite N"  
"n1 \<in> Domain (vcga N G b r)" "n2 \<in> Domain (vcga N G b r)" 
(*"n1 \<noteq> n2"*) 
shows "(vcga N G b r),,n1 \<inter> (vcga N G b r),,n2={}"
using assms sorry (* nitpick [timeout=10000, tac_timeout=45, dont_specialize, show_consts] *)

abbreviation "a00 == hd(perm2 (takeAll (%x. x\<in> set (winningAllocationsAlg N00 (G00) (b00 Else 0))) (possibleAllocationsAlg3 N00 G00)) 1)"
(* abbreviation "a00 == hd(perm2 (takeAll (%x. x\<in> maximalStrictAllocations (int`N00) (G00) (b00 Else 0)) 
(allStrictAllocations N00 G00)) 1)"*)
(*value "tiebids' a00 N00 (set G00) (1,{12})"
value "(maxbid a00 N00 (set G00)) (1,{12})"
value "maximalStrictAllocations' (int`N00) (set G00) (b00 Else 0)"
value "graph a00 (tiebids' a00 N00 (set G00))"*)


lemma nn55: "tiebids' a N G = toFunction (Tiebids a N G)" by simp

corollary mm70f: assumes "finite G" "(a::('a::linorder\<times>_)set) \<in> allStrictAllocations' N G" 
"aa \<in> allStrictAllocations' N G" "aa \<noteq> a" shows 
"setsum' (Tiebids a N G) aa < setsum' (Tiebids a N G) a" using assms mm70d
proof -
term a
let ?f'=Tiebids let ?f=tiebids' let ?s'=setsum' let ?s=setsum let ?g'="?f' a N G" let ?g="?f a N G" 
have "a \<subseteq> Domain ?g' & aa \<subseteq> Domain ?g'" using assms mm64 mm63c
proof -
  have "a \<subseteq> N \<times> (Pow G - {{}}) \<and> aa \<subseteq> N \<times> (Pow G - {{}})"
    using assms(2) assms(3) mm63c by blast
  thus "a \<subseteq> Domain (LinearCompletion (real \<circ> pseudoAllocation a <| (N \<times> finestpart G)) N G) \<and> aa \<subseteq> Domain (LinearCompletion (real \<circ> pseudoAllocation a <| (N \<times> finestpart G)) N G)"
    by fastforce
qed then have 
0: "a \<inter> Domain ?g'=a & aa \<inter> Domain ?g'=aa" by blast moreover have 
1: "finite a & finite aa" using assms by (metis mm44) moreover have 
2: "runiq ?g'"  by (rule mm62)
ultimately moreover have "?s (toFunction ?g') (a \<inter> (Domain ?g')) = ?s' ?g' a" using nn48d by fast
moreover have "?s (toFunction ?g') (aa \<inter> (Domain ?g')) = ?s' ?g' aa" using nn48d 1 2 by blast
ultimately have "?s ?g a = ?s' ?g' a & ?s ?g aa = ?s' ?g' aa" using nn55 by auto 
moreover have "?s ?g aa < ?s ?g a" using assms by (rule mm70d)
ultimately moreover have "?s ?g aa < ?s' ?g' a" by presburger
ultimately show ?thesis by presburger  
qed

end

