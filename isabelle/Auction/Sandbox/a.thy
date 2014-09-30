
theory a

imports Main Random Random_Sequence
f
g
"../Maximum"
(* "../Maskin3"*)
"../CombinatorialAuction"
"../CombinatorialVickreyAuction"            
"~~/src/HOL/Library/Code_Target_Nat"
(*"~~/src/HOL/Library/Permutation"
"~~/src/HOL/Library/Permutations"*)
"~~/src/HOL/Library/Indicator_Function"
(*"~~/../afp-2014-07-13/thys/List-Infinite/ListInf/List2"*) 
(*"~~/src/HOL/Library/DAList"*)

begin

abbreviation "toFunctionWithFallback R fallback == (% x. if (R``{x}={R,,x}) then (R,,x) else fallback)"
notation toFunctionWithFallback (infix "Else" 75)
abbreviation "setsum' R X == setsum (R Else 0) X"
abbreviation "setsum'' R X == setsum (toFunction R) (X \<inter> Domain R)"
abbreviation "setsum''' R X == setsum' R (X\<inter>Domain R)"
abbreviation "setsum'''' R X == setsum (%x. setsum id (R``{x})) X"
(*abbreviation "singleoutside' x f == singleoutside f x"*)
type_synonym bidvector' = "((participant \<times> goods) \<times> price) set"
abbreviation "Participants b' == Domain (Domain b')"

(* abbreviation "vcga N G b == map (toPartialAllo) (winningAllocationsAlg (N \<union> {auctioneer}) G (toFullBid (set G) b))" *)
(* abbreviation "addedBidder (N::participant set) == Min (-N)" *)
(*abbreviation "addedBidder (N::participant set) == 1 + Max N"*)
abbreviation "addedBidder N == (-1::int)"
abbreviation "addedBidder' == (-1::int)"
abbreviation "allStrictAllocations' N G == possibleAllocationsRel N G"
abbreviation "allStrictAllocations'' N \<Omega> == allInjections \<inter> 
{a. Domain a \<subseteq> N & Range a \<in> all_partitions \<Omega>}" 
abbreviation "allStrictAllocations''' N G == allocationsUniverse\<inter> {a. Domain a \<subseteq> N & \<Union> Range a = G}"
lemma nn28: "allStrictAllocations' N G=allStrictAllocations'' N G & 
allStrictAllocations' N G=allStrictAllocations''' N G" using lm19 nn24 by metis
lemma nn28b: "(a \<in> allStrictAllocations''' N G) = (a \<in> allocationsUniverse& Domain a \<subseteq> N & \<Union> Range a = G)"
by force
abbreviation "allAllocations' N \<Omega> == 
(Outside' {addedBidder N}) ` (allStrictAllocations' (N \<union> {addedBidder N}) \<Omega>)"
abbreviation "allAllocations'' N \<Omega> == 
(Outside' {addedBidder N}) ` (allStrictAllocations'' (N \<union> {addedBidder N}) \<Omega>)"
abbreviation "allAllocations''' N \<Omega> == 
(Outside' {addedBidder N}) ` (allStrictAllocations''' (N \<union> {addedBidder N}) \<Omega>)"
lemma nn28c: 
"allAllocations' N G = allAllocations'' N G & allAllocations'' N G = allAllocations''' N G"
using assms nn28 by metis
corollary nn28d: "allAllocations' = allAllocations'' & allAllocations'' = allAllocations'''
& allAllocations' = allAllocations'''" using nn28c by metis
(* abbreviation "allAllocations' N \<Omega> == 
allInjections \<inter> {a. Domain a \<subseteq> (N \<union> {addedBidder N}) & Range a \<in> all_partitions \<Omega>}" *)
lemma nn32: "allAllocations' (N-{addedBidder N}) G \<subseteq> allAllocations' N G" using Outside_def by simp
lemma nn30a: "Range(f outside X) \<supseteq> (Range f)-(f``X)" using assms Outside_def by blast
lemma nn30b: assumes "runiq f" "runiq (f^-1)" shows "Range(f outside X) \<subseteq> (Range f)-(f``X)" using assms
Diff_triv lll78 lll85b Diff_iff ImageE Range_iff subsetI by smt
lemma nn30: assumes "runiq f" "runiq (f^-1)" shows "Range(f outside X) = (Range f)-(f``X)" 
using assms nn30a nn30b by (metis order_class.order.antisym)
corollary lm35d: assumes "a \<in> allocationsUniverse" shows "a outside X \<in> allocationsUniverse" using assms Outside_def
by (metis (lifting, mono_tags) lm35)
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
(EX aa. aa -- (addedBidder N)=a & aa\<in>allStrictAllocations''' (N \<union> {addedBidder N}) G)" by blast

lemma nn37e: assumes "a \<in> allocationsUniverse" "Domain a \<subseteq> N-{addedBidder N}" "\<Union> Range a \<subseteq> G" shows
"a \<in> allAllocations''' N G" using assms nn41 
proof -
let ?i="addedBidder N" let ?Y="{G-\<Union> Range a}-{{}}" let ?b="{?i}\<times>?Y" let ?aa="a\<union>?b"
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
using assms by (metis (full_types) lm19c)

lemma nn37b: assumes "a \<in> allAllocations''' N G" shows "Domain a \<subseteq> N-{addedBidder N} & a \<in> allocationsUniverse"  
proof -
let ?i="addedBidder N" obtain aa where
0: "a=aa -- ?i & aa \<in> allStrictAllocations''' (N \<union> {?i}) G" using assms(1) nn41 by blast
then have "Domain aa \<subseteq> N \<union> {?i}" using nn23 by blast
then have "Domain a \<subseteq> N - {?i}" using 0 Outside_def by blast
moreover have "a \<in> allAllocations' N G" using assms nn28d by metis
then moreover have "a \<in> allocationsUniverse" using nn37 by blast
ultimately show ?thesis by blast
qed

corollary nn37c: assumes "a \<in> allAllocations''' N G" shows 
"a \<in> allocationsUniverse & Domain a \<subseteq> N-{addedBidder N} & \<Union> Range a \<subseteq> G"
proof -
have "a \<in> allocationsUniverse" using assms nn37b by blast
moreover have "Domain a \<subseteq> N-{addedBidder N}" using assms nn37b by blast
moreover have "\<Union> Range a \<subseteq> G" using assms nn40b by blast
ultimately show ?thesis by blast
qed

corollary nn37d: 
"(a\<in>allAllocations''' N G)=(a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder N} & \<Union> Range a \<subseteq> G)" 
using nn37c nn37e by (metis (mono_tags))

lemma nn42: "(a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder N} & \<Union> Range a \<subseteq> G) = 
(a\<in>allocationsUniverse& a\<in>{aa. Domain aa \<subseteq> N-{addedBidder N} & \<Union> Range aa \<subseteq> G})" 
by (metis (lifting, no_types) mem_Collect_eq)

corollary nn37f: "(a\<in>allAllocations''' N G)=
(a\<in>allocationsUniverse& a\<in>{aa. Domain aa \<subseteq> N-{addedBidder N} & \<Union> Range aa \<subseteq> G})" (is "?L = ?R") 
proof -
  have "?L = (a\<in>allocationsUniverse& Domain a \<subseteq> N-{addedBidder N} & \<Union> Range a \<subseteq> G)" by (rule nn37d)
  moreover have "... = ?R" by (rule nn42) ultimately show ?thesis by presburger
qed

corollary nn37g: "a\<in>allAllocations''' N G=
(a\<in> (allocationsUniverse \<inter> {aa. Domain aa \<subseteq> N-{addedBidder N} & \<Union> Range aa \<subseteq> G}))" 
using nn37f by (metis (mono_tags) Int_iff)

abbreviation "allAllocations'''' N G == 
allocationsUniverse\<inter>{aa. Domain aa\<subseteq>N-{addedBidder N} & \<Union>Range aa\<subseteq>G}"

theorem nn44: assumes "a \<in> allAllocations'''' N G" shows "a -- n \<in> allAllocations'''' (N-{n}) G"
proof -
  let ?bb=addedBidder let ?d=Domain let ?r=Range let ?X2="{aa. ?d aa\<subseteq>N-{?bb N} & \<Union>?r aa\<subseteq>G}" 
  let ?X1="{aa. ?d aa\<subseteq>N-{n}-{?bb(N-{n})} & \<Union>?r aa\<subseteq>G}" have "a\<in>?X2" using assms(1) by fast then have 
  0: "?d a \<subseteq> N-{?bb N} & \<Union>?r a \<subseteq> G" by blast then have "?d (a--n) \<subseteq> N-{?bb (N-{n})}-{n}" 
  using outside_reduces_domain by (metis Diff_mono subset_refl) moreover have 
  "... = N-{n}-{?bb (N-{n})}" by fastforce ultimately have 
  "?d (a--n) \<subseteq> N-{n}-{?bb (N-{n})}" by blast moreover have "\<Union> ?r (a--n) \<subseteq> G" 
  unfolding Outside_def using 0 by blast ultimately have "a -- n \<in> ?X1" by fast moreover have 
  "a--n \<in> allocationsUniverse" using assms by (smt Int_iff lm35d) ultimately show ?thesis by blast
qed

corollary ll52b: "(R outside X1) outside X2 = (R outside X2) outside X1" by (metis ll52 sup_commute)

corollary nn37h: "allAllocations''' N G=allAllocations'''' N G"
(is "?L=?R") proof - {fix a have "a \<in> ?L = (a \<in> ?R)" by (rule nn37g)} thus ?thesis by blast qed

theorem nn28e: "allAllocations'=allAllocations'' & allAllocations''=allAllocations''' &
allAllocations'''=allAllocations''''" using nn37h nn28d by metis

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

abbreviation "extendedBid N \<Omega> b == (({addedBidder N} \<times> (Pow \<Omega>)) :== (%x. (0))) b"
abbreviation "maximalAllocations' N \<Omega> b == arg_max' (setsum (extendedBid N \<Omega> b)) (allAllocations' N \<Omega>)"
(* MC: extendedBid superfluous here? *)
abbreviation "maximalAllocations'' N \<Omega> b == arg_max' (setsum b) (allAllocations' N \<Omega>)"
abbreviation "maximalAllocations''' G b == arg_max' (setsum' b) (allAllocations' (Participants b) G)"
abbreviation "maximalStrictAllocations' N G b==
arg_max' (setsum b) (allStrictAllocations' ({addedBidder'}\<union>N) G)"
(*MC: these are the allocations maximizing the revenue, and also including the unallocated goods assigned to
the virtual participant addedBidder. 
Note that commonly b is set to zero identically for such bidder, but this is not formally imposed here.*)
(*abbreviation "allAllocations N G == possibleAllocationsAlg3 N G"
abbreviation "maximalAllocations G b == argmax (setsum' b) ((allAllocations (Participants b) G))"
*)

(*MC: t must come first of toPartialAllo due to how we implemented tie breaking (homogeneously)*)
(* abbreviation "alpha' N G b == (alpha N G) \<circ> (toFullBid G)" 
abbreviation "Vcga N G b t == toPartialAllo (t (Vcgas N G b))"
abbreviation "alpha' N G b == alpha (N\<union>{auctioneer}) G (toFullBid G b)"
abbreviation "alphaAlg' N G b == alphaAlg (N\<union>{auctioneer}) G (toFullBid (set G) b)"
abbreviation "vcgp N G b t n == alpha' N G b n - 
(setsum (toFullBid G b) ((winningAllocationRel (N \<union> {auctioneer}) G t (toFullBid G b)) -- n))"
abbreviation "Vcgp N G b t n == alphaAlg' N G b n - 
(setsum (toFullBid (set G) b) ((winningAllocationAlg (N \<union> {auctioneer}) G t (toFullBid (set G) b)) -- n))"
*)
abbreviation "argmax' f A == { x \<in> A . f x = Max (f ` A) }"
(* abbreviation "Vcga' N G R b == arg_max' (setsum (resolvingBid N G b R)) (set (Vcgas N G b))"
abbreviation "vcgp'' N G b r n == alpha' N (set G) b n - 
(setsum (toFullBid (set G) b) (vcga' N G b r -- n))" *)

corollary lm43d: assumes "a \<in> allocationsUniverse" shows 
"(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> allocationsUniverse" using assms lm43b 
by fastforce

lemma nn27c: "addedBidder (N::participant set) \<notin> int `N" by fastforce
(* abbreviation "randomBids N \<Omega> b random==resolvingBid (N\<union>{addedBidder N}) \<Omega> (extendedBid N (set \<Omega>) b) random" *)
abbreviation "randomBids N \<Omega> b random==resolvingBid (N\<union>{addedBidder N}) \<Omega> b random"
abbreviation "vcga'' N \<Omega> b random == (\<Union>((arg_max' (setsum (randomBids N \<Omega> b random)) (maximalAllocations' N (set \<Omega>) b))))--(addedBidder N)"
abbreviation "vcgp' N \<Omega> b random n ==
(Max (setsum b ` (allAllocations' (N-{n}) (set \<Omega>)))) - (setsum b (vcga'' N \<Omega> b random -- n))"
abbreviation "vcga''' G b r == \<Union>
(arg_max' (setsum (randomBids (Participants b) G (toFunction b) r )) (maximalAllocations''' (set G) b)) 
-- (addedBidder (Participants b))"
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
abbreviation "vcga'''' N G b r == (Union
(arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b))) -- addedBidder'"
lemma nn56: "card X=1 = (X={the_elem X})" 
by (smt card_eq_SucD card_gt_0_imp_non_empty card_insert_disjoint finite.emptyI insert_absorb insert_not_empty the_elem_eq)
lemma nn57: assumes "card X=1" "X \<subseteq> Y" shows "Union X \<in> Y" using assms nn56 by (metis cSup_singleton insert_subset)
corollary nn58: assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"Union
(arg_max' (setsum (randomBids N G b r)) (maximalStrictAllocations' N (set G) b)) \<in>
(maximalStrictAllocations' N (set G) b)" (is "Union ?X \<in> ?R") using assms mm92b nn57
proof -
have "card ?X=1" using assms by (rule mm92b) moreover have "?X \<subseteq> ?R" by auto
ultimately show ?thesis using nn57 by blast
qed

corollary nn58b: assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga'''' N G b r \<in> (Outside' {addedBidder'})`(maximalStrictAllocations' N (set G) b)"
using assms nn58 by blast

lemma nn60: "(x \<in> arg_max' f X) = (x \<in> X & f x = Max {f xx| xx. xx \<in> X})" using arg_max'_def 
by (smt Collect_cong Int_iff image_Collect_mem mem_Collect_eq mm78)

corollary nn59: assumes "finite g" shows "setsum f g = setsum f (g outside X) + (setsum f (g||X))" 
proof -
let ?A="g outside X" let ?B="g||X"
have "finite ?A" using assms(1) Outside_def by (metis finite_Diff)
moreover have "finite ?B" using assms(1) restrict_def by (metis finite_Un outside_union_restrict)
moreover have "?A Int ?B = {}" unfolding Outside_def restrict_def by blast
ultimately show ?thesis using setsum_UN_disjoint by (metis outside_union_restrict setsum.union_disjoint)
qed

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
& (vcga'''' N G b r = a -- addedBidder') 
& (a \<in> arg_max' (setsum b) (allStrictAllocations' ({addedBidder'}\<union>N) (set G)))
)" (is "EX a. _ & _ & a \<in> ?X")
using assms nn58b arg_max'_def by fast

lemma assumes "distinct G" "set G \<noteq> {}" "finite N" shows 
"\<forall>aa\<in>allStrictAllocations' ({addedBidder'}\<union>N) (set G). finite aa"
using assms by (metis List.finite_set mm44)

theorem nn61: assumes "distinct G" "set G \<noteq> {}" "finite N" 
"\<forall>aa\<in>allStrictAllocations' ({addedBidder'}\<union>N) (set G). \<forall> X \<in> Range aa. b (addedBidder', X)=0"
(is "\<forall>aa\<in>?X. _") shows "setsum b (vcga'''' N G b r)=Max{setsum b aa| aa. aa \<in> allAllocations' N (set G)}"
(*MC: adequacy theorem *)
proof -
let ?n=addedBidder' let ?s=setsum let ?a="vcga'''' N G b r" obtain a where 
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
shows "setsum b (vcga'''' N G b r)=Max{setsum b aa| aa. aa \<in> allAllocations' N (set G)}"
using assms nn61 by blast

corollary assumes "distinct G" "set G \<noteq> {}" "finite N" shows
"vcga'''' N G b r \<in> allocationsUniverse & \<Union> Range (vcga'''' N G b r) \<subseteq> set G" using assms nn58b 
proof -
let ?a="vcga'''' N G b r" let ?n=addedBidder'
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

lemma "vcga'''' N G b r = Union ((arg_max' \<circ> setsum) (randomBids N G b r) 
((arg_max' \<circ> setsum) b (allStrictAllocations' ({addedBidder'}\<union>N) (set G)))) -- addedBidder'" by simp
abbreviation "vcgp''' N G b r n ==
(Max (setsum b ` (allAllocations' (N-{n}) (set G)))) - (setsum b (vcga'''' N G b r -- n))"
lemma nn21: "maximalAllocations''' \<Omega> b' \<subseteq> allAllocations' (Participants b') \<Omega>" by auto
abbreviation "chosenAllocation' N G bids random == 
hd(perm2 (takeAll (%x. x\<in>(maximalStrictAllocations' N (set G) bids)) (possibleAllocationsAlg3 
({addedBidder'}\<union>N) G)) random)"
abbreviation "randomBids' N b G r == tiebids' (chosenAllocation' N G b r)
({addedBidder'}\<union>N) (set G)"

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

corollary nn45: assumes "a \<in> allAllocations'''' N G" shows "Range a \<in> allPartitions" using assms 
Outside_def 
by (metis (lifting, mono_tags) Int_iff lm22 mem_Collect_eq)

corollary nn45a: assumes "a \<in> allAllocations' N G" shows "Range a \<in> allPartitions"
proof - have "a \<in> allAllocations'''' N G" using assms nn28e by metis thus ?thesis by (rule nn45) qed


corollary assumes 
"N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" (*MC: why does this emerge only now? *) 
shows "(Outside' {addedBidder N}) ` (terminatingAuctionRel N G (bids) random) = 
{chosenAllocation N G bids random -- (addedBidder N)}" (is "?L=?R") using assms mm92 Outside_def 
proof -
have "?R = Outside' {addedBidder N} ` {chosenAllocation N G bids random}" using Outside_def 
by blast 
moreover have "... = (Outside'{addedBidder N})`(terminatingAuctionRel N G bids random)" using assms mm92 
by blast
ultimately show ?thesis by presburger
qed

abbreviation "argMax X f == arg_max' f X"
lemma "terminatingAuctionRel N G b r = 
((arg_max' (setsum (resolvingBid N G b (nat r)))) \<circ> (arg_max' (setsum b)))
(possibleAllocationsRel N (set G))" by force
term "(Union \<circ> (arg_max' (setsum (resolvingBid N G b (nat r)))) \<circ> (arg_max' (setsum b)))
(possibleAllocationsRel N (set G))"

lemma assumes "addedBidder N \<notin> N" shows "arg_max' (setsum (resolvingBid N G bids (nat random))) (arg_max' (setsum bids) (possibleAllocationsRel N (set G))) = 
arg_max' (setsum (resolvingBid N G bids (nat random))) (arg_max' (setsum bids) (allAllocations'''' N (set G)))"
using assms sorry


corollary nn45b: assumes "a \<in> allAllocations' N G" shows "is_partition (Range a)"
using assms nn45a sorry


lemma nn46: assumes "a \<in> allAllocations'''' N G" shows "runiq a & runiq (a^-1)" using assms nn28e
Int_iff mem_Collect_eq sorry

corollary assumes "a \<in> allAllocations' N (G::good set)" "(n1::participant) \<in> Domain a" "n2 \<in> Domain a"  shows
"(a,,n1) \<inter> (a,,n2) = {}" sorry

corollary assumes "a \<in> allAllocations' N G" "n1 \<in> Domain a" "n2 \<in> Domain a" "n1 \<noteq> n2" shows
"(a,,n1) \<inter> (a,,n2) = {}" using assms nn45a eval_runiq_in_Range nn46 is_partition_def 
is_partition_of_def nn45b
proof - have "runiq a & runiq (a^-1)" using assms nn28e sorry
then have "a,,n1 \<noteq> a,,n2" using assms 
by (metis converse_iff eval_runiq_rel runiq_imp_uniq_right_comp)
moreover have "a,,n1 \<in> Range a & a,,n2 \<in> Range a" using assms 
by (metis `runiq a \<and> runiq (a\<inverse>)` eval_runiq_in_Range)
moreover have "is_partition (Range a)" sorry
ultimately show ?thesis using assms is_partition_def by metis
qed

lemma "arg_max' (setsum' b) = (arg_max' \<circ> setsum') b" by simp

lemma nn47: assumes "runiq f" "x \<in> Domain f" shows "(f Else 0) x = (toFunction f) x" using assms 
by (metis Image_runiq_eq_eval toFunction_def)

lemma nn48b: assumes "runiq f" shows "setsum (f Else 0) (X\<inter>(Domain f)) = setsum (toFunction f) (X\<inter>(Domain f))" 
using assms setsum_cong2 nn47 by fastforce
lemma nn51: assumes "Y \<subseteq> f-`{0}" shows "setsum f Y=0" using assms 
by (metis set_rev_mp setsum.neutral vimage_singleton_eq)
lemma nn49: assumes "Y \<subseteq> f-`{0}" "finite X" shows "setsum f X = setsum f (X-Y)" using assms 
proof -
let ?X0="Y" let ?X1="X\<inter>?X0" let ?X2="X-?X0"
have "finite ?X1" using assms by simp moreover
have "finite ?X2" using assms by simp moreover
have "?X1 \<inter> ?X2={}" by fast
ultimately moreover have "setsum f (?X1 \<union> ?X2) = setsum f ?X1 + (setsum f ?X2)" by (rule setsum_Un_disjoint)
ultimately moreover have "setsum f ?X1 = 0" using assms nn51 by (metis inf.coboundedI2)
ultimately moreover have "setsum f (?X1 \<union> ?X2) = setsum f X" by (metis assms lll23)
ultimately show ?thesis by auto
qed

lemma nn50: "-(Domain f) \<subseteq> (f Else 0)-`{0}" by fastforce

corollary nn52: assumes "finite X" shows "setsum (f Else 0) X=setsum (f Else 0) (X\<inter>Domain f)" proof - 
have "X\<inter>Domain f = X - (-Domain f)" by simp thus ?thesis using assms nn50 nn49 by fastforce qed

corollary nn48c: assumes "finite X" "runiq f" shows "setsum (f Else 0) X = setsum (toFunction f) (X\<inter>Domain f)" 
using assms nn52 nn48b by (smt setsum.cong)

lemma nn53: "setsum (f Else 0) X = setsum' f X" by fast

corollary nn48d: assumes "finite X" "runiq f" shows "setsum (toFunction f) (X\<inter>Domain f) = setsum' f X"
using assms nn53 nn48c by fastforce

lemma assumes "a \<in> allAllocations' N G" shows "a \<union> {(addedBidder N, G-\<Union>Range a)} \<in> allStrictAllocations''' N G"
using assms nn34 sorry

abbreviation "toStrict G allo == allo \<union> {(addedBidder (Domain allo),
(G-\<Union>Range allo) \<union> allo,,,(addedBidder (Domain allo)))}"

lemma nn54a: assumes "a1 \<noteq> a2" "addedBidder (Domain a1) \<notin> (Domain a1) \<union> Domain a2" shows "toStrict G a1 \<noteq> toStrict G a2" 
using assms by blast

lemma nn54b: assumes "toStrict G a1 \<noteq> toStrict G a2" "addedBidder (Domain a1) \<notin> (Domain a1) \<union> Domain a2" shows "a1 \<noteq> a2"
using assms by fast

corollary nn54: assumes "addedBidder (Domain a1) \<notin> (Domain a1) \<union> Domain a2" shows
"a1 \<noteq> a2 = (toStrict G a1 \<noteq> toStrict G a2)" using assms nn54a nn54b by auto 

lemma nn55: "tiebids a N G = toFunction (tiebids' a N G)" by simp

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
ultimately moreover have "?s (toFunction ?g') (a \<inter> (Domain ?g')) = ?s' ?g' a" using nn48d by fast
moreover have "?s (toFunction ?g') (aa \<inter> (Domain ?g')) = ?s' ?g' aa" using nn48d 1 2 by blast
ultimately have "?s ?g a = ?s' ?g' a & ?s ?g aa = ?s' ?g' aa" using nn55 by auto 
moreover have "?s ?g aa < ?s ?g a" using assms by (rule mm70d)
ultimately moreover have "?s ?g aa < ?s' ?g' a" by presburger
ultimately show ?thesis by presburger  
qed

lemma assumes "finite G" "a \<in> allStrictAllocations' (Participants b) G" shows 
"setsum' b a = setsum (toFunction b) a" using assms nn48d sorry

lemma "maximalStrictAllocations' N G b=winningAllocationsRel ({addedBidder'} \<union> N) G b" by fast

lemma 
assumes "finite (Participants b)" "distinct G" "set G \<noteq> {}" shows
"chosenAllocation' G b r \<in> maximalStrictAllocations' (set G) b" using mm82 sorry

corollary
assumes "finite G" "(a::('a::linorder\<times>_)set) \<in> allStrictAllocations' N G" 
"aa \<in> allStrictAllocations' N G" "aa \<noteq> a" shows 
"setsum' (tiebids' a N G) aa < setsum' (tiebids' a N G) a"

corollary mm70e: 
assumes "finite G" 
"addedBidder N \<notin> N"
"a \<in> allAllocations' N G" "aa \<in> allAllocations' N G" "aa \<noteq> a" shows
"setsum' (tiebids' (toStrict G a) (N \<union> {addedBidder N}) G) (toStrict G aa) <
setsum' (tiebids' (toStrict G a) (N \<union> {addedBidder N}) G) (toStrict G a)"
proof -
let ?s=toStrict let ?a="?s G a" let ?aa="?s G aa" let ?S="possibleAllocationsRel (N\<union>{addedBidder N}) G"
have "finite G" using assms(1) 
by simp
moreover have "?a \<in> ?S" using assms sorry
moreover have "?aa \<in> ?S" using assms sorry
moreover have "?aa \<noteq> ?a" using assms nn54 sorry ultimately moreover have 
5: "setsum (tiebids ?a (N\<union>{addedBidder N}) G) ?aa < setsum (tiebids ?a (N\<union>{addedBidder N}) G) ?a" 
by (rule mm70d)
moreover have 
7: "Domain (tiebids' ?a (N\<union>{addedBidder N}) G)=(N\<union>{addedBidder N}) \<times> (Pow G - {{}})"
using mm64 by blast
ultimately moreover have 
6: "?a \<subseteq> (N\<union>{addedBidder N}) \<times> (Pow G - {{}})
& ?aa \<subseteq> (N\<union>{addedBidder N}) \<times> (Pow G - {{}})
" using mm63c 
by (metis (mono_tags))
let ?f="tiebids' ?a (N\<union>{addedBidder N}) G"
let ?ff="tiebids ?a (N\<union>{addedBidder N}) G"
have 
0: "finite ?a" sorry
have 
1: "runiq ?f" sorry
have 
3: "setsum (toFunction ?f) (?a \<inter> Domain ?f) =
setsum' ?f ?a" using 0 1 by (rule nn48d)
have 
2: "finite ?aa" sorry
have 
4: "setsum (toFunction ?f) (?aa \<inter> Domain ?f) =
setsum' ?f ?aa" using 2 1 by (rule nn48d)
have "?a \<subseteq> Domain ?f & ?aa \<subseteq> Domain ?f" using 6 7 by presburger
then have "?a \<inter> Domain ?f = ?a & ?aa \<inter> Domain ?f = ?aa" by blast
then have "setsum ?ff (?aa\<inter>Domain ?f) < setsum ?ff (?a\<inter>Domain ?f)" using 5 
by presburger
then show ?thesis using 3 4 5 6 nn55 by simp
qed


(*
lemma nn07: "\<forall>x \<in> ({auctioneer} \<times> t). (toFullBid G b) x = (%x. 0) x" sorry 

lemma nn08: assumes "finite ({auctioneer} \<times> t)" 
"\<forall>x \<in> ({auctioneer} \<times> t). (toFullBid G b) x = ((%x. 0) x)" 
shows
"setsum (toFullBid G b) ({auctioneer} \<times> t) = setsum (%x. 0) ({auctioneer} \<times> t)" 
using assms by (smt setsum.neutral)

corollary nn09: assumes "trivial t" shows "setsum (toFullBid G b) ({auctioneer} \<times> t) = 0"
using assms nn07 nn08 lm54 sorry

corollary nn09b: "condition1 (toFullBid G b) auctioneer" using assms nn09 by auto

corollary nn10: assumes
"condition1 (toFullBid G b) auctioneer" 
"n \<noteq> auctioneer"
"finite (N \<union> {auctioneer})"
"finite G"
"isChoice (graph {winningAllocationsRel (N\<union>{auctioneer}) G (toFullBid G b)} (t::tieBreaker))"
shows "alpha (N\<union>{auctioneer}) G (toFullBid G b) n \<ge> remainingValueRel (N\<union>{auctioneer}) G t (toFullBid G b) n" 
using assms lm61c by auto

corollary nn10b: assumes "n \<noteq> auctioneer" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel (N\<union>{auctioneer}) G (toFullBid G b)} (t::tieBreaker))"
shows 
"alpha' N G b n \<ge> ((remainingValueRel (N\<union>{auctioneer}) G t (toFullBid G b) n)::price)"
using assms nn10 nn09b by force

lemma nn10c: "x - y >=0 = ((x::price) >= y)" by fastforce

corollary nn10d: assumes "n \<noteq> auctioneer" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel (N\<union>{auctioneer}) G (toFullBid G b)} (t::tieBreaker))"
shows "alpha' N G b n - remainingValueRel (N\<union>{auctioneer}) G t (toFullBid G b) n >=0" 
using assms nn10b nn10c by presburger

lemma nn10e: assumes "f x \<in> x" shows "isChoice (graph {x} f)" by (metis (full_types) Collect_mem_eq assms empty_iff insert_iff lm72)

corollary nn10f: assumes "n \<noteq> auctioneer" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel (N\<union>{auctioneer}) G (toFullBid G b)} (t::tieBreaker))"
shows "vcgp N G b t n >= 0" using assms nn10d by blast

corollary assumes "n \<noteq> auctioneer" "finite N" "finite G" "t (vcgas' N G b) \<in> vcgas' N G b"
shows "vcgp N G b t n >= 0" using assms nn10e nn10f by (metis (lifting)) 

corollary assumes "a \<in> vcgas' N G b" 
shows "(Range a) partitions G" using assms lm47 is_partition_of_def 
by (metis (lifting, no_types) lm03 subsetD)

*)

end

