
theory PartialCombinatorialAuctions

imports 
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
lemma CombiAuction28: "allStrictAllocations' N G=allStrictAllocations'' N G & 
allStrictAllocations' N G=allStrictAllocations''' N G" using lm19 CombiAuction24 by metis
lemma CombiAuction28b: "(a \<in> allStrictAllocations''' N G) = (a \<in> allocationsUniverse& Domain a \<subseteq> N & \<Union> Range a = G)"
by force
abbreviation "allAllocations' N \<Omega> == 
(Outside' {addedBidder'}) ` (allStrictAllocations' (N \<union> {addedBidder'}) \<Omega>)"
abbreviation "allAllocations'' N \<Omega> == 
(Outside' {addedBidder'}) ` (allStrictAllocations'' (N \<union> {addedBidder'}) \<Omega>)"
abbreviation "allAllocations''' N \<Omega> == 
(Outside' {addedBidder'}) ` (allStrictAllocations''' (N \<union> {addedBidder'}) \<Omega>)"
lemma CombiAuction28c: 
"allAllocations' N G = allAllocations'' N G & allAllocations'' N G = allAllocations''' N G"
using assms CombiAuction28 by metis
corollary CombiAuction28d: "allAllocations' = allAllocations'' & allAllocations'' = allAllocations'''
& allAllocations' = allAllocations'''" using CombiAuction28c by metis
lemma CombiAuction32: "allAllocations' (N-{addedBidder'}) G \<subseteq> allAllocations' N G" using Outside_def by simp

lemma CombiAuction34: "(a \<in> allocationsUniverse) = (a \<in> allStrictAllocations''' (Domain a) (\<Union> Range a))"
by blast
lemma CombiAuction35: assumes "N1 \<subseteq> N2" shows "allStrictAllocations''' N1 G \<subseteq> allStrictAllocations''' N2 G" 
using assms by auto
lemma CombiAuction36: assumes "a \<in> allStrictAllocations''' N G" shows "Domain (a -- x) \<subseteq> N-{x}" 
using assms Outside_def by fastforce
lemma CombiAuction37: assumes "a \<in> allAllocations' N G" shows "a \<in> allocationsUniverse"
using assms lm35 Outside_def image_iff CombiAuction24c by smt
lemma CombiAuction38: assumes "a \<in> allAllocations' N G" shows "a \<in> allStrictAllocations''' (Domain a) (\<Union>Range a)"
proof - show ?thesis using assms CombiAuction37 by blast qed
lemma  assumes "N1 \<subseteq> N2" shows "allAllocations''' N1 G \<subseteq> allAllocations''' N2 G"
using assms CombiAuction35 CombiAuction36 CombiAuction37 CombiAuction24c CombiAuction28b CombiAuction28 CombiAuction34 CombiAuction38 Outside_def by blast
lemma CombiAuction39a: "{} \<in> allInjections" by (metis converse_empty mem_Collect_eq runiq_emptyrel)
lemma CombiAuction39b: "{} \<in> allPartitionvalued" by (metis (lifting) Pow_bottom UN_iff lm36b)
(* corollary CombiAuction39: "{} \<in> allocationsUniverse using CombiAuction39a CombiAuction39b by blast*)
lemma lll59b: "runiq (X\<times>{y})" using lll59 by (metis trivial_singleton)
lemma lm37b: "{x}\<times>{y} \<in> allInjections" using lm37 by fastforce
lemma CombiAuction40b: assumes "a \<in> allAllocations''' N G" shows "\<Union> Range a \<subseteq> G" using assms Outside_def by blast
lemma CombiAuction41: "a \<in> allAllocations''' N G = 
(EX aa. aa -- (addedBidder')=a & aa\<in>allStrictAllocations''' (N \<union> {addedBidder'}) G)" by blast

lemma CombiAuction37e: assumes "a \<in> allocationsUniverse" "Domain a \<subseteq> N-{addedBidder'}" "\<Union> Range a \<subseteq> G" shows
"a \<in> allAllocations''' N G" using assms CombiAuction41 
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
(\<Union> Range ?aa)" unfolding CombiAuction34 by metis then have 
"?aa \<in> allStrictAllocations''' (N\<union>{?i}) (\<Union> Range ?aa)" using CombiAuction35 assms paste_def by auto
moreover have "Range ?aa = Range a \<union> ?Y" by blast then moreover have 
"\<Union> Range ?aa = G" using Un_Diff_cancel Un_Diff_cancel2 Union_Un_distrib Union_empty Union_insert  
by (metis (lifting, no_types) assms(3) cSup_singleton subset_Un_eq) moreover have 
"?aa' = ?aa" using 4 by (rule paste_disj_domains)
ultimately have "?aa' \<in> allStrictAllocations''' (N\<union>{?i}) G" by simp
moreover have "Domain ?b \<subseteq> {?i}" by fast then moreover have "?aa' -- ?i = a -- ?i" using ll19 
by (smt Un_empty_right empty_subsetI insert_subset subset_Un_eq subset_antisym subset_insert)
moreover have "... = a" using Outside_def assms(2) by auto 
ultimately show ?thesis using CombiAuction41 by auto
qed

lemma CombiAuction23: 
"a\<in>allStrictAllocations' N \<Omega>=(a\<in>allInjections & Domain a\<subseteq>N & Range a\<in>all_partitions \<Omega>)" 
by (metis (full_types) lm19c)

lemma CombiAuction37b: assumes "a \<in> allAllocations''' N G" shows "Domain a \<subseteq> N-{addedBidder'} & a \<in> allocationsUniverse"  
proof -
let ?i="addedBidder'" obtain aa where
0: "a=aa -- ?i & aa \<in> allStrictAllocations''' (N \<union> {?i}) G" using assms(1) CombiAuction41 by blast
then have "Domain aa \<subseteq> N \<union> {?i}" using CombiAuction23 by blast
then have "Domain a \<subseteq> N - {?i}" using 0 Outside_def by blast
moreover have "a \<in> allAllocations' N G" using assms CombiAuction28d by metis
then moreover have "a \<in> allocationsUniverse" using CombiAuction37 by blast
ultimately show ?thesis by blast
qed

corollary CombiAuction37c: assumes "a \<in> allAllocations''' N G" shows 
"a \<in> allocationsUniverse & Domain a \<subseteq> N-{addedBidder'} & \<Union> Range a \<subseteq> G"
proof -
have "a \<in> allocationsUniverse" using assms CombiAuction37b by blast
moreover have "Domain a \<subseteq> N-{addedBidder'}" using assms CombiAuction37b by blast
moreover have "\<Union> Range a \<subseteq> G" using assms CombiAuction40b by blast
ultimately show ?thesis by blast
qed

corollary CombiAuction37d: 
"(a\<in>allAllocations''' N G)=(a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder'} & \<Union> Range a \<subseteq> G)" 
using CombiAuction37c CombiAuction37e by (metis (mono_tags))

lemma CombiAuction42: "(a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder'} & \<Union> Range a \<subseteq> G) = 
(a\<in>allocationsUniverse& a\<in>{aa. Domain aa \<subseteq> N-{addedBidder'} & \<Union> Range aa \<subseteq> G})" 
by (metis (lifting, no_types) mem_Collect_eq)

corollary CombiAuction37f: "(a\<in>allAllocations''' N G)=
(a\<in>allocationsUniverse& a\<in>{aa. Domain aa \<subseteq> N-{addedBidder'} & \<Union> Range aa \<subseteq> G})" (is "?L = ?R") 
proof -
  have "?L = (a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder'} & \<Union> Range a \<subseteq> G)" by (rule CombiAuction37d)
  moreover have "... = ?R" by (rule CombiAuction42) ultimately show ?thesis by presburger
qed

corollary CombiAuction37g: "a\<in>allAllocations''' N G=
(a\<in> (allocationsUniverse \<inter> {aa. Domain aa \<subseteq> N-{addedBidder'} & \<Union> Range aa \<subseteq> G}))" 
using CombiAuction37f by (metis (mono_tags) Int_iff)

abbreviation "allAllocations'''' N G == 
allocationsUniverse\<inter>{aa. Domain aa\<subseteq>N-{addedBidder'} & \<Union>Range aa\<subseteq>G}"

theorem CombiAuction44: assumes "a \<in> allAllocations'''' N G" shows "a -- n \<in> allAllocations'''' (N-{n}) G"
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

corollary CombiAuction37h: "allAllocations''' N G=allAllocations'''' N G"
(is "?L=?R") proof - {fix a have "a \<in> ?L = (a \<in> ?R)" by (rule CombiAuction37g)} thus ?thesis by blast qed

theorem CombiAuction28e: "allAllocations'=allAllocations'' & allAllocations''=allAllocations''' &
allAllocations'''=allAllocations''''" using CombiAuction37h CombiAuction28d by metis

corollary CombiAuction37i: assumes "G1 \<subseteq> G2" shows "allAllocations'''' N G1 \<subseteq> allAllocations'''' N G2"
using assms by blast

corollary CombiAuction33: assumes "G1 \<subseteq> G2" shows "allAllocations''' N G1 \<subseteq> allAllocations''' N G2"
using assms CombiAuction37i CombiAuction37h 
proof -
have "allAllocations''' N G1 = allAllocations'''' N G1" by (rule CombiAuction37h)
moreover have "... \<subseteq> allAllocations'''' N G2" using assms(1) by (rule CombiAuction37i)
moreover have "... = allAllocations''' N G2" using CombiAuction37h by metis
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

lemma CombiAuction27c: "addedBidder' \<notin> int `N" by fastforce

abbreviation "randomBids N \<Omega> b random==resolvingBid (N\<union>{addedBidder'}) \<Omega> b random"

theorem mm92b: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"card (arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b))=1"
(*MC: Here we are showing that our way of randomizing using randomBids actually breaks the tie:
we are left with a singleton after the tiebreaking round*)
(is "card ?L=_") proof -
let ?n="{addedBidder'}" have 
1: "(?n \<union> N)\<noteq>{}" by simp have 
4: "finite (?n\<union>N)" using assms(3) by fast have 
"terminatingAuctionRel (?n\<union>N) G b r = {chosenAllocation (?n\<union>N) G b r}" using 1 assms(1) 
assms(2) 4 by (rule mm92) moreover have "?L = terminatingAuctionRel (?n\<union>N) G b r" by auto
ultimately show ?thesis by auto
qed
lemma "arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b) \<subseteq> 
maximalStrictAllocations' N (set G) b" by auto
abbreviation "vcga' N G b r == (Union
(arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b))) -- addedBidder'"

corollary CombiAuction58: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"Union
(arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b)) \<in>
(maximalStrictAllocations' N (set G) b)" (is "Union ?X \<in> ?R") using assms mm92b CombiAuction57
proof -
have "card ?X=1" using assms by (rule mm92b) moreover have "?X \<subseteq> ?R" by auto
ultimately show ?thesis using CombiAuction57 by blast
qed

corollary CombiAuction58b: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga' N G b r \<in> (Outside' {addedBidder'})`(maximalStrictAllocations' N (set G) b)"
using assms CombiAuction58 by blast

lemma CombiAuction62: "(Outside' {addedBidder'})`(maximalStrictAllocations' N G b) \<subseteq> allAllocations' N G"
using Outside_def by force

theorem CombiAuction58d: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga' N G b r \<in> allAllocations' N (set G)" (is "?a \<in> ?A") using assms CombiAuction58b CombiAuction62 
proof - have "?a \<in> (Outside' {addedBidder'})`(maximalStrictAllocations' N (set G) b)" 
using assms by (rule CombiAuction58b) thus ?thesis using CombiAuction62  by fastforce qed

corollary CombiAuction59b: assumes "\<forall>X. X \<in> Range a \<longrightarrow>b (addedBidder', X)=0" "finite a" shows 
"setsum b a = setsum b (a--addedBidder')"
proof -
let ?n=addedBidder' have "finite (a||{?n})" using assms restrict_def by (metis finite_Int) 
moreover have "\<forall>z \<in> a||{?n}. b z=0" using assms restrict_def by fastforce
ultimately have "setsum b (a||{?n}) = 0" using assms by (metis setsum.neutral)
thus ?thesis using CombiAuction59 assms(2) by (metis comm_monoid_add_class.add.right_neutral)
qed

corollary CombiAuction59c: assumes "\<forall>a\<in>A. finite a & (\<forall> X. X\<in>Range a \<longrightarrow> b (addedBidder', X)=0)"
shows "{setsum b a| a. a\<in>A}={setsum b (a -- addedBidder')| a. a\<in>A}" using assms CombiAuction59b 
by (metis (lifting, no_types))
corollary CombiAuction58c: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"EX a. ((a \<in> (maximalStrictAllocations' N (set G) b)) 
& (vcga' N G b r = a -- addedBidder') 
& (a \<in> arg_max' (setsum b) (allStrictAllocations' ({addedBidder'}\<union>N) (set G)))
)" (is "EX a. _ & _ & a \<in> ?X")
using assms CombiAuction58b arg_max'_def by fast

lemma assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"\<forall>aa\<in>allStrictAllocations' ({addedBidder'}\<union>N) (set G). finite aa"
using assms by (metis List.finite_set mm44)

theorem CombiAuction61: assumes "distinct G" "set G \<noteq> {}" "finite N" 
"\<forall>aa\<in>allStrictAllocations' ({addedBidder'}\<union>N) (set G). \<forall> X \<in> Range aa. b (addedBidder', X)=0"
(is "\<forall>aa\<in>?X. _") shows "setsum b (vcga' N G b r)=Max{setsum b aa| aa. aa \<in> allAllocations' N (set G)}"
(*MC: adequacy theorem *)
proof -
let ?n=addedBidder' let ?s=setsum let ?a="vcga' N G b r" obtain a where 
0: "a \<in> maximalStrictAllocations' N (set G) b & ?a=a--?n & 
(a\<in>arg_max' (setsum b) (allStrictAllocations'({addedBidder'}\<union>N)(set G)))"(is "_ & ?a=_ & a\<in>?Z")
using assms(1,2,3) CombiAuction58c by blast have 
1: "\<forall>aa\<in>?X. finite aa & (\<forall> X. X\<in>Range aa \<longrightarrow> b (?n, X)=0)" using assms(4) 
List.finite_set mm44 by metis have 
2: "a \<in> ?X" using 0 by auto have "a \<in> ?Z" using 0 by fast 
then have "a \<in> ?X\<inter>{x. ?s b x = Max (?s b ` ?X)}" using mm78 by simp
then have "?s b a = Max {?s b aa| aa. aa\<in>?X}" using Collect_cong Int_iff image_Collect_mem mem_Collect_eq by smt
moreover have "{?s b aa| aa. aa\<in>?X} = {?s b (aa--?n)| aa. aa\<in>?X}" using 1 by (rule CombiAuction59c)
moreover have "... = {?s b aa| aa. aa \<in> Outside' {?n}`?X}" by blast
moreover have "... = {?s b aa| aa. aa \<in> allAllocations' N (set G)}" by simp
ultimately have "Max {?s b aa| aa. aa \<in> allAllocations' N (set G)} = ?s b a" by presburger
moreover have "... = ?s b (a--?n)" using 1 2 CombiAuction59b by (metis (lifting, no_types))
ultimately show "?s b ?a=Max{?s b aa| aa. aa \<in> allAllocations' N (set G)}" using 0 by presburger
qed

























































corollary CombiAuction61b: assumes "distinct G" "set G \<noteq> {}" "finite N" "\<forall> X. b (addedBidder', X)=0" 
shows "setsum b (vcga' N G b r)=Max{setsum b aa| aa. aa \<in> allAllocations' N (set G)}"
using assms CombiAuction61 by blast

corollary CombiAuction58e: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"vcga' N G b r \<in> allocationsUniverse & \<Union> Range (vcga' N G b r) \<subseteq> set G" using assms CombiAuction58b 
proof -
let ?a="vcga' N G b r" let ?n=addedBidder'
obtain a where 
0: "?a=a -- addedBidder' & a \<in> maximalStrictAllocations' N (set G) b"
using assms CombiAuction58b by blast
then moreover have 
1: "a \<in> allStrictAllocations' ({?n}\<union>N) (set G)" by auto
moreover have "maximalStrictAllocations' N (set G) b \<subseteq> allocationsUniverse" 
by (metis (lifting, mono_tags) lm03 lm50 subset_trans)
ultimately moreover have "?a=a -- addedBidder' & a \<in> allocationsUniverse" by blast
then have "?a \<in> allocationsUniverse" using lm35d by auto
moreover have "\<Union> Range a= set G" using CombiAuction24d 1 by metis
then moreover have "\<Union> Range ?a \<subseteq> set G" using Outside_def 0 by fast
ultimately show ?thesis using lm35d Outside_def by blast
qed

lemma "vcga' N G b r = Union ((arg_max' \<circ> setsum) (randomBids N G b r) 
((arg_max' \<circ> setsum) b (allStrictAllocations' ({addedBidder'}\<union>N) (set G)))) -- addedBidder'" by simp
abbreviation "vcgp' N G b r n ==
(Max (setsum b ` (allAllocations' (N-{n}) (set G)))) - (setsum b (vcga' N G b r -- n))"

lemma CombiAuction63: assumes "x \<in> X" "finite X" shows "Max (f`X) >= f x" (is "?L >= ?R") using assms 
by (metis (hide_lams, no_types) Max.coboundedI finite_imageI image_eqI)

theorem CombiAuction44b: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcgp' N G (b::_=>price) r n >= 0" 
proof - 
let ?a="vcga' N G b r" let ?A=allAllocations' let ?A'=allAllocations'''' let ?f="setsum b" 
have "?a \<in> ?A N (set G)" using assms by (rule CombiAuction58d)
then have "?a \<in> ?A' N (set G)" using CombiAuction28e by metis then have "?a -- n \<in> ?A' (N-{n}) (set G)" by (rule CombiAuction44) 
then have "?a -- n \<in> ?A (N-{n}) (set G)" using CombiAuction28e by metis
moreover have "finite (?A (N-{n}) (set G))" 
by (metis List.finite_set assms(3) finite.emptyI finite_Diff finite_Un finite_imageI finite_insert lm59) 
ultimately have "Max (?f`(?A (N-{n}) (set G))) >= ?f (?a -- n)" (is "?L >= ?R") by (rule CombiAuction63)
then have "?L - ?R >=0" by linarith thus ?thesis by fast
qed

lemma lm19b: "allStrictAllocations' N G = possibleAllocationsRel N G" using assms by (metis lm19)
abbreviation "strictAllocationsUniverse == allocationsUniverse"

abbreviation "N00 == {1,2::nat}"
abbreviation "G00 == [11::nat, 12, 13]"
abbreviation "A00 == {(0,{10,11::nat}), (1,{12,13})}"
abbreviation "b00 == 
{
((1::int,{11}),3),
((1,{12}),0),
((1::participant,{11,12::nat}),4::price),
((2,{11}),2),
((2,{12}),2),
((2,{11,12}),1)
}"

abbreviation "Goods bids == \<Union>((snd\<circ>fst)`bids)"

corollary CombiAuction45: assumes "a \<in> allAllocations'''' N G" shows "Range a \<in> allPartitions" using assms 

by (metis (lifting, mono_tags) Int_iff lm22 mem_Collect_eq)

corollary CombiAuction45a: assumes "a \<in> allAllocations' N G" shows "Range a \<in> allPartitions"
proof - have "a \<in> allAllocations'''' N G" using assms CombiAuction28e by metis thus ?thesis by (rule CombiAuction45) qed

corollary assumes 
"N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" (*MC: why does this emerge only now? *) 
shows "(Outside' {addedBidder'}) ` (terminatingAuctionRel N G (bids) random) = 
{chosenAllocation N G bids random -- (addedBidder')}" (is "?L=?R") using assms mm92 Outside_def 
proof -
have "?R = Outside' {addedBidder'} ` {chosenAllocation N G bids random}" using Outside_def 
by blast 
moreover have "... = (Outside'{addedBidder'})`(terminatingAuctionRel N G bids random)" using assms mm92 
by blast
ultimately show ?thesis by presburger
qed

abbreviation "argMax X f == arg_max' f X"
lemma "terminatingAuctionRel N G b r = 
((arg_max' (setsum (resolvingBid N G b (nat r)))) \<circ> (arg_max' (setsum b)))
(possibleAllocationsRel N (set G))" by force
term "(Union \<circ> (arg_max' (setsum (resolvingBid N G b (nat r)))) \<circ> (arg_max' (setsum b)))
(possibleAllocationsRel N (set G))"

lemma CombiAuction55: "tiebids a N G = toFunction (tiebids' a N G)" by simp

lemma "maximalStrictAllocations' N G b=winningAllocationsRel ({addedBidder'} \<union> N) G b" by fast

corollary mm70f: assumes "finite G" "(a::('a::linorder\<times>_)set) \<in> allStrictAllocations' N G" 
"aa \<in> allStrictAllocations' N G" "aa \<noteq> a" shows 
"setsum' (tiebids' a N G) aa < setsum' (tiebids' a N G) a" using assms mm70d
proof -
term a
let ?f'=tiebids' let ?f=tiebids let ?s'=setsum' let ?s=setsum let ?g'="?f' a N G" let ?g="?f a N G" 
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
ultimately moreover have "?s (toFunction ?g') (a \<inter> (Domain ?g')) = ?s' ?g' a" using CombiAuction48d by fast
moreover have "?s (toFunction ?g') (aa \<inter> (Domain ?g')) = ?s' ?g' aa" using CombiAuction48d 1 2 by blast
ultimately have "?s ?g a = ?s' ?g' a & ?s ?g aa = ?s' ?g' aa" using CombiAuction55 by auto 
moreover have "?s ?g aa < ?s ?g a" using assms by (rule mm70d)
ultimately moreover have "?s ?g aa < ?s' ?g' a" by presburger
ultimately show ?thesis by presburger  
qed

lemma CombiAuction64: assumes "a \<in> allocationsUniverse" 
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

lemma CombiAuction64c: assumes "a \<in> allocationsUniverse" 
"n1 \<in> Domain a" "n2 \<in> Domain a"
"n1 \<noteq> n2" 
shows "a,,,n1 \<inter> a,,,n2={}" using assms CombiAuction64 lll82 by fastforce 

theorem CombiAuction_PairwiseDisjointAllocations:
assumes "distinct G" "set G \<noteq> {}" "finite N"  
"n1 \<in> Domain (vcga' N G b r)" "n2 \<in> Domain (vcga' N G b r)" "n1 \<noteq> n2" 
shows "(vcga' N G b r),,,n1 \<inter> (vcga' N G b r),,,n2={}"  
proof -
have "vcga' N G b r \<in> allocationsUniverse" using CombiAuction58e assms by blast
thus ?thesis using CombiAuction64c assms by fast
qed

(* lemma assumes "n \<in> Domain a" "a \<in> allAllocations' N G" "G\<noteq>{}" shows "a,,n \<noteq> {}"
using assms sledgehammer
*)

lemma assumes "R,,,x \<noteq> {}" shows "x \<in> Domain R" using assms  
proof - have "\<Union> (R``{x}) \<noteq> {}" using assms(1) by fast
then have "R``{x} \<noteq> {}" by fast thus ?thesis by blast qed

lemma assumes "runiq f" and "x \<in> Domain f" shows "(f ,, x) \<in> Range f" using assms 
by (rule eval_runiq_in_Range)

theorem CombiAuction_OnlyGoodsAllocated: assumes "distinct G" "set G \<noteq> {}" "finite N" "g \<in> (vcga' N G b r),,,n" 
shows "g \<in> set G" 
proof - 
let ?a="vcga' N G b r" 
have "?a \<in> allocationsUniverse" using assms(1,2,3) CombiAuction58e by blast
then have "runiq ?a" using assms(1,2,3) by blast
moreover have "n \<in> Domain ?a" using assms(4) eval_rel_def by fast
ultimately moreover have "?a,,n \<in> Range ?a" using eval_runiq_in_Range by fast 
ultimately have "?a,,,n \<in> Range ?a" using lll82 by fastforce
then have "g \<in> \<Union> Range ?a" using assms by blast 
moreover have "\<Union> Range ?a \<subseteq> set G" using assms(1,2,3) CombiAuction58e by fast
ultimately show ?thesis by blast
qed

(* theorem CombiAuction_PairwiseDisjointAllocations_Counter:
assumes "distinct G" "set G \<noteq> {}" "finite N"  
"n1 \<in> Domain (vcga' N G b r)" "n2 \<in> Domain (vcga' N G b r)" 
shows "(vcga' N G b r),,,n1 \<inter> (vcga' N G b r),,,n2={}" 
nitpick [card int = 1, card nat = 1, card "int \<times> 'a set" = 1, 
         card "'a set list \<times> 'a set list" = 1, 
         card "'b option" = 1, card "nat list list" = 1,
         card "'a set list list" = 1, card "('a set \<times> int) set list list" = 1,
    card "'a set list list list" = 1, card "real list" = 1,  card "real option" = 1,
    card "'a list" = 1,   card "'a" = 1,  card "int list" = 1, card "nat list" = 1,
    card "'a set list" = 1, card "(int \<times> 'a set) set list" = 1,
    card "('a set \<times> int) set list" = 1,  card "'b" = 1, 
verbose, show_consts]

proof -
have "vcga' N G b r \<in> allocationsUniverse" using CombiAuction58e assms by blast
thus ?thesis using CombiAuction64c assms by fast
qed *)

(* theorem counterexample_CombiAuction64c: assumes "a \<in> allocationsUniverse" 
"n1\<in> Domain a" "n2 \<in> Domain a"
shows "a,,,n1 \<inter> a,,,n2={}" nitpick
*)
(*
value "LinearCompletion (b00 Else 0) (int`N00) (set G00)"
  
abbreviation "a00 == hd(perm2 (takeAll (%x. x\<in> set (winningAllocationsAlg N00 (G00) (b00 Else 0))) (possibleAllocationsAlg3 N00 G00)) 1)"
value a00
value "maxbid a00 N00 (set G00)"

value "graph a00 (tiebids a00 N00 (set G00))"
*)
end

