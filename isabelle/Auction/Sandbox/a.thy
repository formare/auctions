
theory a

imports Main Random Random_Sequence
g
"../Maximum"
"../Maskin3"
"../CombinatorialVickreyAuction"            
"~~/src/HOL/Library/Code_Target_Nat"
(*"~~/src/HOL/Library/Permutation"
"~~/src/HOL/Library/Permutations"*)
"~~/src/HOL/Library/Indicator_Function"
(*"~~/../afp-2014-07-13/thys/List-Infinite/ListInf/List2"*) 
(*"~~/src/HOL/Library/DAList"*)

begin
abbreviation "Fun_upd X g == (%f x. if x \<in> X then (g x) else f x)"
notation Fun_upd (infix ":==" 80)
abbreviation "auctioneer == 0::participant"
abbreviation "seller == auctioneer"
(*MC: converters*)
(* abbreviation "toFullBid Goods (bids::altbids) == (({auctioneer} \<times> Pow (Goods)) :== (%x. (0::price))) bids" *)
abbreviation "toFullBid Goods (bids::altbids) == (({auctioneer} \<times> (Pow Goods)) :== (%x. (0::price))) bids"
term "toFullBid G b"
(* MC: restore previous definition, after changing condition1 *)
abbreviation "toPartialAllo a == a -- auctioneer"
term "winningAllocationsAlg N G "
(* abbreviation "vcga N G b == map (toPartialAllo) (winningAllocationsAlg (N \<union> {auctioneer}) G (toFullBid (set G) b))" *)
abbreviation "vcgas N G b == winningAllocationsRel (N \<union> {auctioneer}) G (toFullBid G b)"
abbreviation "Vcgas N G b == winningAllocationsAlg (N \<union> {auctioneer}) G (toFullBid (set G) b)"
abbreviation "vcga N G b t == toPartialAllo (t (vcgas N G b))" 
(*MC: t must come first of toPartialAllo due to how we implemented tie breaking (homogeneously)*)
(* abbreviation "alpha' N G b == (alpha N G) \<circ> (toFullBid G)" *)
abbreviation "Vcga N G b t == toPartialAllo (t (Vcgas N G b))"
abbreviation "alpha' N G b == alpha (N\<union>{auctioneer}) G (toFullBid G b)"
abbreviation "alphaAlg' N G b == alphaAlg (N\<union>{auctioneer}) G (toFullBid (set G) b)"
abbreviation "vcgp N G b t n == alpha' N G b n - 
(setsum (toFullBid G b) ((winningAllocationRel (N \<union> {auctioneer}) G t (toFullBid G b)) -- n))"
abbreviation "Vcgp N G b t n == alphaAlg' N G b n - 
(setsum (toFullBid (set G) b) ((winningAllocationAlg (N \<union> {auctioneer}) G t (toFullBid (set G) b)) -- n))"
term "alpha N G b (n::participant)"
lemma "alpha' N G b n = alpha (N\<union>{auctioneer}) G (toFullBid G b) (n::participant)" by fast
lemma "alpha' N G b n = Max ((setsum (toFullBid G b))`(possibleAllocationsRel ((N\<union>{auctioneer})-{n}) G))"
by fast
term "(Vcga N G b t)::allocation"

lemma nn07: "\<forall>x \<in> ({auctioneer} \<times> t). (toFullBid G b) x = (%x. 0) x" sorry 

lemma nn08: assumes "finite ({auctioneer} \<times> t)" 
"\<forall>x \<in> ({auctioneer} \<times> t). (toFullBid G b) x = ((%x. 0) x)" 
shows
"setsum (toFullBid G b) ({auctioneer} \<times> t) = setsum (%x. 0) ({auctioneer} \<times> t)" 
using assms 
by (smt setsum_cong2)

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

corollary assumes "n \<noteq> auctioneer" "finite N" "finite G" "t (vcgas N G b) \<in> vcgas N G b"
shows "vcgp N G b t n >= 0" using assms nn10e nn10f by (metis (lifting)) 

corollary assumes "a \<in> vcgas N G b" 
shows "(Range a) partitions G" using assms lm47 is_partition_of_def 
by (metis (lifting, no_types) lm03 subsetD)

lemma n12: "Range (toPartialAllo a) \<subseteq> Range a" 
by (metis Range_outside_sub subset_refl)

lemma nn11: assumes "\<Union> P = X" shows "P \<subseteq> Pow X" using assms by blast

corollary nn12a: assumes "t (vcgas N G b) \<in> vcgas N G b" shows "is_partition (Range (vcga N G b t))"
using assms lm47 is_partition_of_def Range_outside_sub subset_refl by (smt in_mono lm03 subset_is_partition)

corollary nn12b: assumes "t (vcgas N G b) \<in> vcgas N G b" shows "Range (vcga N G b t) \<subseteq> Pow G"
using assms in_mono lm03 lm47 is_partition_of_def nn11 Range_outside_sub  by (metis (lifting, no_types))

corollary nn12: assumes "t (vcgas N G b) \<in> vcgas N G bcon" 
(*this is an assumption about t, not about b, G or N*)
shows "is_partition (Range (vcga N G b t)) & Range (vcga N G b t) \<subseteq> Pow G"
using assms nn12a nn12b by fast

lemma mm85: "arg_max' f {x} = {x}" using arg_max'_def by auto

lemma mm86: assumes "finite A" "A \<noteq> {}" shows "Max (f`A) \<in> f`A" using assms 
by (metis Max_in finite_imageI image_is_empty)
 
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
using assms mm90b lm59 arg_max'_non_empty_iff by (metis lm03 rev_finite_subset)


lemma mm71: "x \<in> X = ({x} \<in> finestpart X)" using finestpart_def by force

lemma "arg_max' f A \<subseteq> f -` {Max (f ` A)}" by force

lemma mm78: "arg_max' f A = A \<inter>{ x . f x = Max (f ` A) }" by auto

lemma mm10: assumes "runiq f" "X \<subseteq> Domain f" shows 
"graph X (toFunction f) = (f||X)" using assms graph_def toFunction_def Outside_def 
restrict_def
by (smt Collect_mono Domain_mono Int_commute eval_runiq_rel ll37 ll41 ll81 restrict_ext restriction_is_subrel set_rev_mp subrel_runiq)

lemma mm11: assumes "runiq f" shows 
"graph (X \<inter> Domain f) (toFunction f) = (f||X)" using assms mm10 
by (metis Int_lower2 restriction_within_domain)

lemma mm65:"{(x, f x)| x. x \<in> X2} || X1 = {(x, f x)| x. x \<in> X2 \<inter> X1}" using graph_def lm05 by metis
lemma mm51: "Range -` {{}} = {{}}" by auto
lemma mm52: "possibleAllocationsRel N {} \<subseteq> {{}}" using emptyset_part_emptyset3 mm51 
by (smt lm28b mem_Collect_eq subsetI vimage_def)
(* lemma "possibleAllocationsRel N {} \<supseteq> {{}}" using lm31 lm28b emptyset_part_emptyset3 mm51 
mem_Collect_eq subsetI vimage_def *)

lemma mm47: "(\<forall> pair \<in> a. finite (snd pair)) = (\<forall> y \<in> Range a. finite y)" by fastforce

lemma mm38c: "inj_on fst P = inj_on snd (P^-1)" using Pair_inject
by (smt converse.intros converseE inj_on_def surjective_pairing)

lemma mm39: assumes "runiq (a^-1)" shows "setsum (card \<circ> snd) a = setsum card (Range a)" 
using assms setsum.reindex lll33 mm38c converse_converse by (metis snd_eq_Range)

lemma mm29: assumes "X \<noteq> {}" shows "finestpart X \<noteq> {}" using assms finestpart_def by blast

lemma assumes "f \<in> allPartitionvalued" shows "{} \<notin> Range f" using assms by (metis lm22 no_empty_eq_class)

lemma mm33: assumes "finite XX" "\<forall>X \<in> XX. finite X" "is_partition XX" shows 
"card (\<Union> XX) = setsum card XX" using assms is_partition_def card_Union_disjoint by fast

corollary mm33b: assumes "XX partitions X" "finite X" "finite XX" shows 
"card (\<Union> XX) = setsum card XX" using assms mm33 by (metis is_partition_of_def lll41)

lemma assumes "inj_on g X" shows "setsum f (g`X) = setsum (f \<circ> g) X" using assms by (metis setsum.reindex)

lemma mm31: assumes "X \<noteq> Y" shows "{{x}| x. x \<in> X} \<noteq> {{x}| x. x \<in> Y}" using assms by auto

corollary mm31b: "inj_on finestpart UNIV" using mm31 ll64 by (metis (lifting, no_types) injI)

lemma mm60: assumes "runiq R" "z \<in> R" shows "R,,(fst z) = snd z" 
using assms runiq_def eval_rel_def by (metis l31 surjective_pairing)

lemma mm59: assumes "runiq R" shows "setsum (toFunction R) (Domain R) = setsum snd R" using 
assms toFunction_def setsum_reindex_cong mm60 lll31 by (metis (no_types) fst_eq_Domain)
corollary mm59b: assumes "runiq (f||X)" shows "setsum (toFunction (f||X)) (X \<inter> Domain f) =
setsum snd (f||X)" using assms mm59 by (metis Int_commute ll41)
lemma "(R||X) `` X = R``X" 
by (metis Int_absorb lll02 lll85 lll99)
lemma mm61: assumes "x \<in> Domain (f||X)" shows "(f||X)``{x} = f``{x}" using assms
lll02 lll85 lll99 by (metis Int_empty_right Int_iff Int_insert_right_if1 ll41)
lemma mm61b: assumes "x \<in> X \<inter> Domain f" "runiq (f||X)" shows "(f||X),,x = f,,x" 
using assms lll02 lll85 Int_empty_right Int_iff Int_insert_right_if1 eval_rel.simps by metis

lemma mm61c: assumes "runiq (f||X)" shows 
"setsum (toFunction (f||X)) (X \<inter> Domain f) = setsum (toFunction f) (X \<inter> Domain f)" 
using assms setsum_cong2 mm61b toFunction_def by metis
corollary mm59c: assumes "runiq (f||X)" shows 
"setsum (toFunction f) (X \<inter> Domain f) = setsum snd (f||X)" using assms mm59b mm61c by fastforce

corollary assumes "runiq (f||X)" shows "setsum (toFunction (f||X)) (X \<inter> Domain f) = setsum snd (f||X)" 
using assms mm59 restrict_def ll41 Int_commute by metis
lemma mm26: "card (finestpart X) = card X" 
using finestpart_def by (metis (lifting) card_image inj_on_inverseI the_elem_eq)
corollary mm26b: "finestpart {} = {} & card \<circ> finestpart = card" using mm26 finestpart_def by fastforce

lemma mm40: "finite (finestpart X) = finite X" using assms finestpart_def mm26b by (metis card_eq_0_iff empty_is_image finite.simps mm26)
lemma "finite \<circ> finestpart = finite" using mm40 by fastforce

lemma mm43: assumes "runiq f" shows "finite (Domain f) = finite f" 
using assms Domain_empty_iff card_eq_0_iff finite.emptyI lll34 by metis

lemma mm42: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "finite (Range a)" using assms lm47 
lm55 by (metis lm28)

corollary mm44: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "finite a"
using assms mm42 mm43 lm47 injections_def by (smt finite_converse mem_Collect_eq)

lemma mm45: assumes "XX \<in> allPartitionvalued" shows "{} \<notin> Range XX" using assms 
mem_Collect_eq no_empty_eq_class by auto

corollary mm45b: assumes "a \<in> possibleAllocationsRel N G" shows "{} \<notin> Range a" using assms mm45 
lm50 by blast

lemma assumes "a \<in> possibleAllocationsRel N G" shows "\<Union> Range a = G" using assms 
by (metis is_partition_of_def lm47)

lemma mm41: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows
"\<forall> y \<in> Range a. finite y" using assms is_partition_of_def lm47 by (metis Union_upper rev_finite_subset)

corollary mm33c: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"card G = setsum card (Range a)" using assms mm33b mm42 lm47 by (metis is_partition_of_def)

lemma mm24: "setsum ((curry f) x) Y = setsum f ({x} \<times> Y)"
proof -
let ?f="% y. (x, y)" let ?g="(curry f) x" let ?h=f
have "inj_on ?f Y" by (metis Pair_inject inj_onI) 
moreover have "{x} \<times> Y = ?f ` Y" by fast
moreover have "\<forall> y. y \<in> Y \<longrightarrow> ?g y = ?h (?f y)" by simp
ultimately show ?thesis using setsum_reindex_cong by metis
qed

lemma mm24b: "setsum (%y. f (x,y)) Y = setsum f ({x} \<times> Y)" using assms mm24 by (smt Sigma_cong curry_def setsum.cong)

abbreviation "Chi X Y == (Y \<times> {0::nat}) +* (X \<times> {1})"
notation Chi (infix "<||" 80)
abbreviation "chii X Y == toFunction (X <|| Y)"
notation chii (infix "<|" 80)
abbreviation "chi X == indicator X"

lemma mm13: "runiq (X <|| Y)" by (metis lll59 runiq_paste2 trivial_singleton)

corollary mm12: assumes "finite X" shows "setsum f X = setsum f (X-Y) + (setsum f (X \<inter> Y))" 
using assms Diff_iff IntD2 Un_Diff_Int finite_Un inf_commute setsum.union_inter_neutral by metis

corollary "(P +* Q) `` (X \<inter> (Domain Q))= Q``X"  by (metis Image_within_domain Int_commute ll50)

corollary mm19: assumes "X \<inter> Domain Q = {}" (is "X \<inter> ?dq={}") shows "(P +* Q) `` X = (P outside ?dq)`` X" 
using assms ll50 ll25 paste_def l38 Outside_def 
by (metis Diff_disjoint Image_empty Image_within_domain Un_Image sup_inf_absorb)

lemma mm20: assumes  "X \<inter> Y = {}"  shows "(P outside Y)``X=P``X"
using assms Outside_def by blast

corollary mm19b: assumes "X \<inter> Domain Q = {}" shows "(P +* Q) `` X = P``X" 
using assms mm19 mm20 by metis

lemma mm14b: "runiq ((X \<times> {x}) +* (Y \<times> {y}))" using assms lll59 trivial_singleton runiq_paste2 by metis

lemma mm14c: assumes "x \<in> X" shows "1 \<in> (X <|| Y) `` {x}" using assms toFunction_def 
paste_def Outside_def runiq_def mm14b by blast

lemma mm14d: assumes "x \<in> Y-X" shows "0 \<in> (X <|| Y) `` {x}" using assms toFunction_def
paste_def Outside_def runiq_def mm14b by blast

lemma l31b: assumes "y \<in> f``{x}" "runiq f" shows "f,,x = y" using assms
by (metis Image_singleton_iff l31)

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
using assms mm12 mm18 by (smt mm17)

corollary mm21: assumes "finite Z" shows "setsum (chi X) Z = card (X \<inter> Z)" using assms 
setsum_indicator_eq_card by (metis Int_commute)

corollary mm22: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "setsum (X <| Y) Z = card (Z \<inter> X)"
using assms mm21 by (metis mm15 setsum_indicator_eq_card)

corollary mm28: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "(setsum (X <| Y) X) - (setsum (X <| Y) Z) =
card X - card (Z \<inter> X)" using assms mm22 by (metis Int_absorb2 Un_upper1 card_infinite equalityE setsum.infinite)

corollary mm28b: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "int (setsum (X <| Y) X) - int (setsum (X <| Y) Z) =
int (card X) - int (card (Z \<inter> X))" using assms mm22 by (metis Int_absorb2 Un_upper1 card_infinite equalityE setsum.infinite)

lemma mm23: assumes "finite X" "finite Y" "card (X \<inter> Y) = card X" shows "X \<subseteq> Y" using assms 
by (metis Int_lower1 Int_lower2 card_seteq order_refl)

lemma mm23b: assumes "finite X" "finite Y" "card X = card Y" shows "(card (X \<inter> Y)=card X) = (X = Y)"
using assms mm23 by (metis card_seteq le_iff_inf order_refl)
term allAllocations





















abbreviation "N00 == {1,2::nat}"
abbreviation "G00 == [11::nat, 12, 13]"
abbreviation "A00 == {(0,{10,11::nat}), (1,{12,13})}"
abbreviation "b00 == 
{
((1,{11}),3),
((1,{12}),0),
((1::participant,{11,12::nat}),4::price),
((2,{11}),2),
((2,{12}),2),
((2,{11,12}),1)
}"

abbreviation "b11 == toFunction ((N00 \<times> (Pow (set G00)))\<times>{0} +* b00)"

abbreviation "omega pair == {fst pair} \<times> (finestpart (snd pair))"
abbreviation "pseudoAllocation allocation == \<Union> (omega ` allocation)"
abbreviation "allocation2Goods allocation == \<Union> (snd ` allocation)"
abbreviation "bidMaximizedBy allocation (N::participant set) (G::goods) == 
(* (N \<times> finestpart G) \<times> {0::price} +* ((pseudoAllocation allocation) \<times> {1}) *)
pseudoAllocation allocation <|| (N \<times> (finestpart G))"
abbreviation "maxbid a N G == toFunction (bidMaximizedBy a N G)"
abbreviation "partialCompletionOf bids pair == (pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))"
abbreviation "LinearCompletion bids N G == (partialCompletionOf bids) ` (N \<times> (Pow G - {{}}))"
abbreviation "linearCompletion bids N G == toFunction (LinearCompletion bids N G)"
abbreviation "tiebids a N G == linearCompletion (maxbid a N G) N G"
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
corollary mm57b: "inj_on (partialCompletionOf bids) X" using mm57 by (metis (lifting) fst_conv inj_on_inverseI)
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
using assms mm26 mm27 by (metis card_cartesian_product_singleton)

lemma mm30: assumes "{} \<notin> Range f" "runiq f" shows "is_partition (omega ` f)"
(* MC: generalize and clean *)
proof -
let ?X="omega ` f" let ?p=finestpart
  { fix y1 y2; assume "y1 \<in> ?X & y2 \<in> ?X"
    then obtain pair1 pair2 where 
    0: "y1 = omega pair1 & y2 = omega pair2 & pair1 \<in> f & pair2 \<in> f" by blast
    then moreover have "snd pair1 \<noteq> {} & snd pair1 \<noteq> {}" using assms
by (metis rev_image_eqI snd_eq_Range)
    ultimately moreover have "fst pair1 = fst pair2 \<longleftrightarrow> pair1 = pair2" using assms runiq_def 
by (metis runiq_imp_uniq_right_comp surjective_pairing)
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
shows "card (pseudoAllocation a) = setsum (card \<circ> omega) a" 
using assms mm33 mm32 setsum.reindex by smt

lemma mm35: "card (omega pair)= card (snd pair)" using mm26 card_cartesian_product_singleton 
by metis

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
shows "int (setsum (maxbid a N G) (pseudoAllocation a)) - 
int (setsum (maxbid a N G) (pseudoAllocation aa)) = 
int (card (pseudoAllocation a)) - int (card (pseudoAllocation aa \<inter> (pseudoAllocation a)))" using mm28b assms
by blast

lemma mm50: "pseudoAllocation {} = {}" by simp

corollary mm53b: assumes "a \<in> possibleAllocationsRel N {}" shows "(pseudoAllocation a)={}"
using assms mm52 by blast

corollary mm53: assumes "a \<in> possibleAllocationsRel N G" "finite G" "G \<noteq> {}"
shows "finite (pseudoAllocation a)" using assms mm48 card_eq_0_iff by smt

corollary mm54: assumes "a \<in> possibleAllocationsRel N G" "finite G"
shows "finite (pseudoAllocation a)" using assms mm53 mm53b Sigma_empty1 empty_iff finite_SigmaI
by (metis (mono_tags))

lemma mm56: assumes "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G" "finite G" shows 
"(card (pseudoAllocation aa \<inter> (pseudoAllocation a)) = card (pseudoAllocation a)) = 
(pseudoAllocation a = pseudoAllocation aa)" using assms mm48 mm23b 
proof -
let ?P=pseudoAllocation let ?c=card let ?A="?P a" let ?AA="?P aa"
have "?c ?A=?c G & ?c ?AA=?c G" using assms by (metis (lifting, no_types) mm48)
moreover have "finite ?A & finite ?AA" using assms mm54 by blast
ultimately show ?thesis using assms mm23b by smt
qed

lemma mm55: "omega pair = {fst pair} \<times> {{y}| y. y \<in> snd pair}" 
using finestpart_def ll64 by auto

lemma mm55b: "{(fst pair, {y})| y. y \<in>  snd pair} = {fst pair} \<times> {{y}| y. y \<in> snd pair}" by fastforce

lemma mm55c: "omega pair = {(fst pair, {y})| y. y \<in>  snd pair}" using mm55 mm55b by metis

lemma mm55d: "pseudoAllocation a = \<Union> {{(fst pair, {y})| y. y \<in> snd pair}| pair. pair \<in> a}"
using mm55c by blast
lemma mm55e: "\<Union> {{(fst pair, {y})| y. y \<in> snd pair}| pair. pair \<in> a}=
{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" by blast

lemma mm55f: "pseudoAllocation a = {(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" using mm55d 
mm55e by (metis (full_types))
lemma mm55j: "{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a} = 
{(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a}"
using finestpart_def by fastforce
corollary mm55k: "pseudoAllocation a = {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a}" 
using mm55f mm55j by blast
lemma mm55u: assumes "runiq a" shows 
"{(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a} = {(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
(is "?L=?R") using assms mm55k runiq_def by (smt Collect_cong Domain.DomainI fst_conv mm60 runiq_wrt_ex1 surjective_pairing)
corollary mm55v: assumes "runiq a" shows "pseudoAllocation a = {(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
using assms mm55u mm55k by fastforce
lemma mm55l: "Range {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a} = 
{Y. EX y. ((Y \<in> finestpart y) & (y \<in> Range a))}" by auto
lemma mm55m: "{Y. EX y. ((Y \<in> finestpart y) & (y \<in> Range a))} = 
\<Union> (finestpart ` (Range a))" by auto
corollary mm55t: "Range (pseudoAllocation a) = \<Union> (finestpart ` (Range a))" 
using mm55k mm55l mm55m by fastforce
lemma mm55n: assumes "X \<subseteq> Y" shows "finestpart X \<subseteq> finestpart Y" using assms finestpart_def by (metis image_mono)
corollary mm55o: assumes "x \<in> X" shows "finestpart x \<subseteq> finestpart (\<Union> X)" using assms
mm55n by (metis Union_upper)
lemma mm55p: "\<Union> (finestpart ` XX) \<subseteq> finestpart (\<Union> XX)" using assms finestpart_def 
mm55o by force
lemma (*UGLY*) mm55q: "\<Union> (finestpart ` XX) \<supseteq> finestpart (\<Union> XX)" (is "?L \<supseteq> ?R") using assms finestpart_def mm55o 
proof -
let ?f=finestpart
{
  fix X assume "X \<in> ?R" then obtain x where 
  0: "x \<in> \<Union> XX & X={x}" using finestpart_def by (metis (lifting) imageE)
  then obtain Y where "Y \<in> XX & x \<in> Y & X={x}" by blast
  then have "Y\<in> XX & X \<in> finestpart Y" using finestpart_def by auto
  then have "X \<in> ?L" by blast  
}
then show ?thesis by force
qed
corollary mm55r: "\<Union> (finestpart ` XX) = finestpart (\<Union> XX)" using mm55p mm55q by fast
corollary mm55s: "Range (pseudoAllocation a) = finestpart (\<Union> Range a)" using mm55r mm55t by metis 
lemma mm55g: "{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}=
{(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a}" by auto

lemma mm55i: "pseudoAllocation a = {(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a}"
using mm55f mm55g Collect_cong by smt

lemma mm55h: assumes "runiq a" shows "{(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a} = 
{(x, {y})| x y. y \<in> a,,x & x \<in> Domain a}" using assms Image_runiq_eq_eval by fast

(*
lemma assumes "{} \<notin> Range a2" "{} \<notin> Range a1" "xx \<in> Domain a2 - (Domain a1)" shows 
"{(x, {y})| x y. y \<in> a1,,x & x \<in> Domain a1} \<noteq>
{(x, {y})| x y. y \<in> a2,,x & x \<in> Domain a2}" using assms 
                       
lemma assumes "a1 \<noteq> a2" "runiq a1" "runiq a2" shows "pseudoAllocation a1 \<noteq> pseudoAllocation a2" 
using assms mm55f inj_on_def runiq_def mm55h 

corollary assumes "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
"finite G" shows
"setsum (maxbid a N G) (pseudoAllocation a) - setsum (maxbid a N G) (pseudoAllocation aa) = 0 
= (a=aa)" 
*)

lemma mm62: "runiq (LinearCompletion bids N G)" using assms by (metis graph_def image_Collect_mem ll37)
corollary mm62b: "runiq (LinearCompletion bids N G || a)" using mm62 by (smt Pair_inject imageE runiq_restrict)
lemma mm64: "N \<times> (Pow G - {{}}) = Domain (LinearCompletion bids N G)" by blast
lemma mm63: assumes "a \<in> possibleAllocationsRel N G" shows "Range a \<subseteq> Pow G"
using assms lm50 lm47 injections_def is_partition_of_def by (metis subset_Pow_Union)
corollary mm63b: assumes "a \<in> possibleAllocationsRel N G" shows "Domain a \<subseteq> N & Range a \<subseteq> Pow G - {{}}" using
assms mm63 insert_Diff_single mm45b subset_insert by (metis insert_absorb lm47 subset_trans)
corollary mm63c: assumes "a \<in> possibleAllocationsRel N G" shows "a \<subseteq> N \<times> (Pow G - {{}})" 
using assms mm63b by blast
corollary mm63d: assumes "a \<in> possibleAllocationsRel N G" shows "a \<subseteq> Domain (LinearCompletion bids N G)"
proof -
let ?p=possibleAllocationsRel let ?L=LinearCompletion
have "a \<subseteq> N \<times> (Pow G - {{}})" using assms mm63c by presburger
moreover have "N \<times> (Pow G - {{}})=Domain (?L bids N G)" using mm64 by fast
ultimately show ?thesis by blast
qed

corollary mm59d: "setsum (linearCompletion bids N G) (a \<inter> (Domain (LinearCompletion bids N G))) = 
setsum snd ((LinearCompletion bids N G) || a)" using assms mm59c mm62b by fast

corollary mm59e: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion bids N G) a = setsum snd ((LinearCompletion bids N G) || a)" 
proof -
let ?l=linearCompletion let ?L=LinearCompletion
have "a \<subseteq> Domain (?L bids N G)" using assms by (rule mm63d) then
have "a = a \<inter> Domain (?L bids N G)" by blast then
have "setsum (?l bids N G) a = setsum (?l bids N G) (a \<inter> Domain (?L bids N G))" by presburger
thus ?thesis using mm59d by auto
qed

(* lemma assumes "a \<subseteq> N \<times> (Pow G - {{}})" shows 
"LinearCompletion bids N G || a \<supseteq> (partialCompletionOf bids) ` a" 
using assms restrict_def by fast *)
corollary mm59f: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion bids N G) a = setsum snd ((partialCompletionOf bids) ` ((N \<times> (Pow G - {{}})) \<inter> a))"
(is "?X=?R")
proof -
let ?p=partialCompletionOf let ?L=LinearCompletion let ?l=linearCompletion
let ?A="N \<times> (Pow G - {{}})" let ?inner2="(?p bids)`(?A \<inter> a)" let ?inner1="(?L bids N G)||a"
have "?R = setsum snd ?inner1" using assms mm66d by (metis (no_types))
moreover have "setsum (?l bids N G) a = setsum snd ?inner1" using assms by (rule mm59e)
ultimately show ?thesis by presburger
qed
corollary mm59g: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion bids N G) a = setsum snd ((partialCompletionOf bids) ` a)" (is "?L=?R")
using assms mm59f mm63c 
proof -
let ?p=partialCompletionOf let ?l=linearCompletion
have "?L = setsum snd ((?p bids)`((N \<times> (Pow G - {{}}))\<inter> a))" using assms by (rule mm59f)
moreover have "... = ?R" using assms mm63c by (metis (lifting, no_types) Int_absorb1)
ultimately show ?thesis by presburger
qed
corollary mm57c: "setsum snd ((partialCompletionOf bids) ` a) = setsum (snd \<circ> (partialCompletionOf bids)) a"
using assms setsum_reindex mm57b by blast
corollary mm59h: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion bids N G) a = setsum (snd \<circ> (partialCompletionOf bids)) a" (is "?L=?R")
using assms mm59g mm57c 
proof -
let ?p=partialCompletionOf let ?l=linearCompletion
have "?L = setsum snd ((?p bids)` a)" using assms by (rule mm59g)
moreover have "... = ?R" using assms mm57c by blast
ultimately show ?thesis by presburger
qed
corollary mm25c: assumes "a \<in> possibleAllocationsRel N G" shows 
"setsum (linearCompletion bids N G) a = setsum ((setsum bids) \<circ> omega) a" (is "?L=?R") 
using assms mm59h mm25 
proof -
let ?inner1="snd \<circ> (partialCompletionOf bids)" let ?inner2="(setsum bids) \<circ> omega"
let ?M="setsum ?inner1 a"
have "?L = ?M" using assms by (rule mm59h)
moreover have "?inner1 = ?inner2" using mm25 assms by fastforce
ultimately show "?L = ?R" using assms by metis
qed

corollary mm25d: assumes "a \<in> possibleAllocationsRel N G" shows
"setsum (linearCompletion bids N G) a = setsum (setsum bids) (omega` a)"
using assms mm25c setsum_reindex mm32 
proof -
have "{} \<notin> Range a" using assms by (metis mm45b)
then have "inj_on omega a" using mm32 by blast
then have "setsum (setsum bids) (omega ` a) = setsum ((setsum bids) \<circ> omega) a" 
by (rule setsum_reindex)
moreover have "setsum (linearCompletion bids N G) a = setsum ((setsum bids) \<circ> omega) a"
using assms mm25c by (rule Extraction.exE_realizer)
ultimately show ?thesis by presburger
qed

lemma mm67: assumes "finite (snd pair)" shows "finite (omega pair)" using assms 
by (metis finite.emptyI finite.insertI finite_SigmaI mm40)
corollary mm67b: assumes "\<forall>y\<in>(Range a). finite y" shows "\<forall>y\<in>(omega ` a). finite y"
using assms mm67 by (smt imageE mm47)
lemma assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "\<forall>y \<in> (Range a). finite y"
using assms by (metis mm41)

corollary setsum_Union_disjoint_2: assumes "\<forall>x\<in>X. finite x" "is_partition X" shows
"setsum f (\<Union> X) = setsum (setsum f) X" using assms setsum_Union_disjoint is_partition_def by fast

corollary setsum_Union_disjoint_3: assumes "\<forall>x\<in>X. finite x" "X partitions XX" shows
"setsum f XX = setsum (setsum f) X" using assms by (metis is_partition_of_def setsum_Union_disjoint_2)

corollary setsum_associativity: assumes "finite x" "X partitions x" shows
"setsum f x = setsum (setsum f) X" using assms setsum_Union_disjoint_3 by (metis is_partition_of_def lll41)

corollary mm67c: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "\<forall>x\<in>(omega ` a). finite x" 
using assms mm67b mm41 by smt

corollary mm30b: assumes "a \<in> possibleAllocationsRel N G" shows "is_partition (omega ` a)"
using assms mm30 mm45b image_iff lll81a by smt

lemma mm68: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"setsum (setsum bids) (omega` a) = setsum bids (\<Union> (omega ` a)) " 
using assms setsum_Union_disjoint_2 mm30b mm67c mm41 by (metis (lifting, no_types))

corollary mm69: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"setsum (linearCompletion bids N G) a = setsum bids (pseudoAllocation a)" (is "?L = ?R")
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
using assms mm73 lm47 mm55s lm47 is_partition_of_def subset_trans by smt
corollary mm73c: assumes "a \<in> possibleAllocationsRel N G" shows "pseudoAllocation a \<subseteq> N \<times> finestpart G" using assms mm73b 
proof -
let ?p=pseudoAllocation let ?aa="?p a" let ?d=Domain let ?r=Range
have "?d ?aa \<subseteq> N" using assms mm73b by presburger
moreover have "?r ?aa \<subseteq> finestpart G" using assms mm73b by simp
ultimately have "?d ?aa \<times> (?r ?aa) \<subseteq> N \<times> finestpart G" by auto
then show "?aa \<subseteq> N \<times> finestpart G" by auto
qed

lemma mm49b: assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
shows "setsum (maxbid a N G) (pseudoAllocation a) - setsum (maxbid a N G) (pseudoAllocation aa) = 
card G - card (pseudoAllocation aa \<inter> (pseudoAllocation a))"
using assms mm48 mm49 mm54 mm73c mm54 
proof -
let ?p=pseudoAllocation let ?f=finestpart let ?m=maxbid let ?B="?m a N G" 
have "?p aa \<subseteq> N \<times> ?f G" using assms mm73c by presburger
then have "?p aa \<subseteq> ?p a \<union> (N \<times> ?f G)" by auto
moreover have "finite (?p aa)" using assms mm48 by (metis (lifting, no_types) mm54)
ultimately have "setsum ?B (?p a) - setsum ?B (?p aa) = card (?p a) - card (?p aa \<inter> (?p a))"
using mm49 by presburger
moreover have "... = card G - card (?p aa \<inter> (?p a))" using assms mm48 by auto
ultimately show ?thesis by presburger
qed

lemma mm49d: assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
shows "int (setsum (maxbid a N G) (pseudoAllocation a)) - int (setsum (maxbid a N G) (pseudoAllocation aa)) = 
int (card G) - int (card (pseudoAllocation aa \<inter> (pseudoAllocation a)))" 
proof -
let ?p=pseudoAllocation let ?f=finestpart let ?m=maxbid let ?B="?m a N G" 
have "?p aa \<subseteq> N \<times> ?f G" using assms mm73c by presburger
then have "?p aa \<subseteq> ?p a \<union> (N \<times> ?f G)" by auto
moreover have "finite (?p aa)" using assms mm48 by (metis (lifting, no_types) mm54)
ultimately have "int (setsum ?B (?p a)) - int (setsum ?B (?p aa)) = int (card (?p a)) - card (?p aa \<inter> (?p a))"
using mm49c by presburger
moreover have "... = int (card G) - card (?p aa \<inter> (?p a))" using assms mm48 by auto
ultimately show ?thesis by presburger
qed

































corollary mm70: 
assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
shows "setsum (linearCompletion (maxbid a N G) N G) a - setsum (linearCompletion (maxbid a N G) N G) aa = 
card G - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" (is "?L=?R") 
proof -
  let ?l=linearCompletion let ?m=maxbid let ?s=setsum let ?p=pseudoAllocation
  have "?s (?l (?m a N G) N G) a = ?s (?m a N G) (?p a) &
  ?s (?l (?m a N G) N G) aa = ?s (?m a N G) (?p aa)" using assms mm69 by blast
  moreover have "?R = ?s (?m a N G) (?p a) - (?s (?m a N G) (?p aa))" using assms mm49b by presburger
  ultimately moreover have "... = ?L" by presburger
  ultimately show ?thesis by presburger
qed

corollary mm70b: 
assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
shows "int (setsum (tiebids a N G) a) - int (setsum (tiebids a N G) aa) = 
int (card G) - int (card (pseudoAllocation aa \<inter> (pseudoAllocation a)))" (is "?L=?R") 
proof -
  let ?l=linearCompletion let ?m=maxbid let ?s=setsum let ?p=pseudoAllocation
  have "?s (?l (?m a N G) N G) a = ?s (?m a N G) (?p a) &
  ?s (?l (?m a N G) N G) aa = ?s (?m a N G) (?p aa)" using assms mm69 by blast
  moreover have "?R = int (?s (?m a N G) (?p a)) - int ((?s (?m a N G) (?p aa)))" using assms mm49d by presburger  
  ultimately moreover have "... = ?L" by presburger
  ultimately show ?thesis by presburger
qed

abbreviation "mbc pseudo == {(x, \<Union> (pseudo `` {x}))| x. x \<in> Domain pseudo}"

lemma mm74: assumes "inj_on f Y" "X \<subseteq> Y" shows "inj_on (image f) (Pow X)" using assms 
by (smt PowD inj_onI inj_on_image_eq_iff subset_inj_on) 
corollary assumes "{} \<notin> Range X" shows "inj_on (image omega) (Pow X)" using assms mm74 mm32 by blast
lemma mm75: "X=\<Union> (finestpart X)" using ll64 by auto
lemma mm75b: "Union \<circ> finestpart = id" using finestpart_def mm75 by fastforce
lemma mm75c: "inj_on Union (finestpart ` UNIV)" using assms finestpart_def mm75b by (metis inj_on_id inj_on_imageI)
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
lemma mm75f: assumes "f \<circ> g=id" shows "inj_on g UNIV" using assms 
by (metis inj_on_id inj_on_imageI2)
corollary mm75g: "inj_on pseudoAllocation (runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}})))" 
using mm75e inj_on_imageI2 by blast
lemma mm76: "allInjections \<subseteq> runiqs" using runiqs_def Collect_conj_eq Int_assoc Int_lower1 by metis
lemma mm77: "allPartitionvalued \<subseteq> Pow (UNIV \<times> (UNIV - {{}}))" using assms is_partition_def by force
corollary mm75i: "allAllocations \<subseteq> runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}}))" using mm76 mm77 by auto
corollary mm75h: "inj_on pseudoAllocation allAllocations" using assms mm75g mm75i subset_inj_on by blast
corollary mm75j: "inj_on pseudoAllocation (possibleAllocationsRel N G)" using subset_inj_on mm75h by (smt lm50)
(*
lemma "(image omega) ` UNIV \<subseteq> finestpart ` UNIV" 
lemma "inj_on pseudoAllocation UNIV" using assms mm32 mm75c 
lemma assumes "pseudoAllocation a1 = pseudoAllocation a2" "{} \<notin> Range a1" "{} \<notin> Range a2" 
shows "a1 \<subseteq> a2" using assms mm32 
lemma  assumes "{} \<notin> Range f" "runiq f" shows "is_partition (omega ` f)" using assms
rev_image_eqI snd_eq_Range assms runiq_def runiq_imp_uniq_right_comp surjective_pairing 
Int_absorb Times_empty insert_not_empty is_partition_def  inf_commute inf_sup_aci(1) 
*)

lemma assumes "card X = 1" shows "X = {the_elem X}" using assms by (smt card_eq_SucD the_elem_eq)
lemma assumes "card X\<ge>1" "\<forall>x\<in>X. y > x" shows "y > Max X" using assms
card_ge_0_finite card_gt_0_imp_non_empty Max_in by smt

lemma mm80: assumes "finite X" "mx \<in> X" "\<forall>x \<in> X-{mx}. f x < f mx" shows "arg_max' f X = {mx}" 
proof -
let ?A="arg_max'" let ?XX="?A f X" let ?Y="f ` X" let ?M="Max ?Y" have "\<forall>x \<in> X. f x \<le> f mx" 
using assms(3) by (metis (full_types) Diff_iff empty_iff insert_iff less_imp_le not_less) 
then have "f mx = ?M" using assms(1,2) 
by (metis (hide_lams, mono_tags) Max_eqI finite_imageI image_iff)
then have "mx \<in> ?XX" by (smt arg_max'.simps assms(2) mem_Collect_eq)
thus ?thesis using assms arg_max'_def by force
qed

corollary mm80c: "(finite X & mx \<in> X & (\<forall>aa \<in> X-{mx}. f aa < f mx)) \<longrightarrow> arg_max' f X = {mx}"
using assms mm80 by metis

corollary mm80b: assumes "finite X" "mx \<in> X" "\<forall>x \<in> X. x \<noteq> mx \<longrightarrow> f x < f mx" shows "arg_max' f X = {mx}"
using assms mm80 by (metis Diff_iff insertI1)

corollary mm70c: assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
"x=int (setsum (tiebids a N G) a) - int (setsum (tiebids a N G) aa)" shows
"x <= card G & x \<ge> 0 & (x=0 \<longleftrightarrow> a = aa) & (aa \<noteq> a \<longrightarrow> setsum (tiebids a N G) aa < setsum (tiebids a N G) a)"
proof -
let ?p=pseudoAllocation have 
1: "x \<le> card G" using assms mm70b by force have 
0: "card (?p aa) = card G & card (?p a) = card G" using assms by (metis (lifting, no_types) mm48)
moreover have "finite (?p aa) & finite (?p a)" using assms mm54 by blast ultimately
have "card (?p aa \<inter> ?p a) \<le> card G" using Int_lower2 card_mono by fastforce then have 
2: "x \<ge> 0" using assms mm70b by force have "card (?p aa \<inter> (?p a)) = card G \<longleftrightarrow> (?p aa = ?p a)" 
using 0 by (metis (lifting, no_types) assms(1) assms(2) assms(3) mm56)
moreover have "?p aa = ?p a \<longrightarrow> a = aa" using assms mm75j inj_on_def by (metis (lifting, no_types))
ultimately have "card (?p aa \<inter> (?p a)) = card G \<longleftrightarrow> (a=aa)" by blast
moreover have "x = int (card G) - card (?p aa \<inter> (?p a))" using assms mm70b by presburger
ultimately have 
3: "x = 0 \<longleftrightarrow> (a=aa)" by linarith then have 
"aa \<noteq> a \<longrightarrow> setsum (tiebids a N G) aa < setsum (tiebids a N G) a" using 1 2 assms by force
thus ?thesis using 1 2 3 by force
qed 

corollary mm70d: assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
"aa \<noteq> a" shows "setsum (tiebids a N G) aa < setsum (tiebids a N G) a" using assms mm70c 
by presburger

lemma assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "setsum (maxbid a N G) a = card G"
using assms sorry







































lemma assumes "\<forall>x. x \<in> X \<longrightarrow> finite (snd x)" "finite X" 
"is_partition (snd ` X)" shows 
"setsum (card \<circ> snd) X = card (\<Union> (snd ` X))" using assms sorry

lemma assumes "allocation \<in> allAllocations" shows
"is_partition (omega ` allocation)" using assms is_partition_def sorry

lemma assumes "finite G" "finite N" "a \<in> possibleAllocationsRel N G" shows 
"card (pseudoAllocation a) = card G" 
using assms possible_allocations_rel_def injections_def all_partitions_def sorry

lemma assumes "finite a" "\<forall>x \<in> a. finite (snd x)" shows "finite (pseudoAllocation a)" 
using assms sorry

lemma "pseudoAllocation a \<subseteq> (Domain a \<times> (finestpart (\<Union> Range a)))" 
using assms finestpart_def sorry

lemma assumes "!x. x \<in> Range a \<longrightarrow> finite x" "is_partition (Range a)" shows 
"card (pseudoAllocation a) = card (\<Union> Range a)"
using assms is_partition_def mm26 sorry

lemma mm08: assumes "finite X" shows 
"setsum f X <= card X * Max (Range (graph X f)) & 
setsum f X <= card X * Max (Range (graph X f))" using assms graph_def sorry

lemma mm09: assumes "finite a" "finite N" "finite G" shows 
"Min (Range (bidMaximizedBy a N G || a)) >= 1 &
Max (Range (bidMaximizedBy a N G || a)) <= 1" using assms Range_def paste_def
sorry

lemma assumes "runiq f" shows "Graph (toFunction f) \<supseteq> f" using assms Graph_def toFunction_def 
runiq_def sorry

lemma "setsum f X = setsum f (X - (f -` {0}))" using assms sorry

lemma assumes "finite aa" shows "proceeds (toFunction (bidMaximizedBy aa N G)) a = 
proceeds (toFunction (bidMaximizedBy aa N G)) (a \<inter> aa)"
using assms mm10 mm09 mm08 sorry

lemma assumes "finite a1" "runiq (a1^-1)" "\<Union> (snd ` a1) = G" "Domain a1=N" shows 
"proceeds (toFunction (bidMaximizedBy a1 N G)) a1 = card a1 * Max (Range ((bidMaximizedBy a1 N G)))"
using assms runiq_def mm08 mm09 mm10 sorry

lemma assumes "runiq (a2^-1)" "runiq (a1^-1)" "\<Union> (snd ` a1) = G" "\<Union> (snd ` a2) = G" shows 
"proceeds (toFunction (bidMaximizedBy a1 N G)) a2 >= card G"
using assms runiq_def sorry








































fun prova where "prova f X 0 = X" | "prova f X (Suc n) = f n (prova f X n)"

fun prova2 where "prova2 f 0 = UNIV" |"prova2 f (Suc n) = f n (prova2 f n)"

lemma assumes "card X > 0" "finite X" "\<forall> n. card (prova f X (n+1)) < card (prova f X n)" 
shows "\<forall>m. EX n. card (prova f X n)<=1"
using assms prova_def sorry

abbreviation "pred5 (m::nat) == \<forall>f. ((f (0::nat)=m & (\<forall>n. (f n - 1 >= f (Suc n)))) \<longrightarrow> (f (f 0))<=(0::nat))"

lemma mm00: "pred5 (0::nat)" by fastforce

lemma mm01: assumes "pred5 m" shows "pred5 (Suc m)"
proof -
{ 
  fix f::"nat => nat" let ?g="%n. f n - 1"   
  {
    assume 
    3: "f (Suc m) > 0" assume 
    2: "(f (0::nat)=Suc m & (\<forall>n. (f n - 1 >= f (Suc n))))"     
    then moreover have "\<forall>n. (?g n - 1 >= ?g (Suc n))" by (metis diff_le_mono)
    ultimately have "?g 0=m & (\<forall>n. (?g n - 1 >= ?g (Suc n)))" by force then have 
    5: "?g (?g 0) \<le> 0" using assms by auto
    moreover have "f m > f(f 0)" using 3 2 by smt
    ultimately have "f (?g 0) - 1 \<ge> f (f 0)" using 2 by auto
    then have "?g (?g 0) \<ge> f (f 0)" by fast
    then have "f (f 0) \<le> 0" using 5 by simp
  }  
}
then show ?thesis using assms by (metis le_less_linear)
qed

lemma mm01b: "\<forall>k::nat. (pred5 k \<longrightarrow> pred5 (Suc k))" using mm01 by fast

lemma mm02: "\<forall>m::nat. pred5 m" using assms mm00 mm01b lll20 nat_induct 
proof -
{
    fix P::"nat => bool" assume 
    23: "P=pred5"
    then have "P (0::nat) & (!k::nat. (P k \<longrightarrow> P (Suc k)))" 
    using mm00 mm01b by fast
    then have "!n::nat. (P n)" using nat_induct by auto
}
thus ?thesis by presburger
qed

lemma mm02b: assumes "\<forall>n. (f n - 1 >= f (Suc n))" shows "f (f 0)<=(0::nat)" using mm02 assms by blast

fun geniter where "geniter f 0 = f 0" | "geniter f (Suc n)=(f (Suc n)) o (geniter f n)"

abbreviation "pseudodecreasing X Y == card X - 1 \<le> card Y - 2"
(* We'll use this to model the behaviour {1,2,3} -> {1,2} -> {1} -> {1} -> {1} ... *)
notation pseudodecreasing (infix "<~" 75)

lemma mm03: assumes "\<forall>X. f (n+1) X <~ X" shows 
"geniter f (n+1) X <~ geniter f n X" using assms geniter_def 
proof -
let ?g=geniter
have "?g f (n+1) X = f (n+1) (?g f n X)" using geniter_def by simp
moreover have "f (n+1) (?g f n X) <~ ?g f n X" using assms by fast
ultimately show "?g f (n+1) X <~ ?g f n X" by simp 
then have "card (?g f (n+1) X) - 1 \<le> card (?g f n X) - 2" by fast
let ?h="%n. card (?g f n X) - 1"
qed

lemma mm04: assumes "\<forall>n. \<forall>X. f (n+1) X <~ X" shows "\<forall>n. geniter f (n+1) X <~ geniter f n X" using assms mm03 by blast

lemma mm05: assumes "\<forall>n. \<forall>X. f (n+1) X <~ X" shows "card (geniter f (card (geniter f 0 X) - 1) X) - 1 <= 0" 
proof -
let ?g=geniter let ?h="%n. card (?g f n X) - 1"
have "\<forall>n. ?h (Suc n) <= ?h n - 1" using assms by (metis Suc_1 Suc_eq_plus1 diff_diff_left mm03)
thus ?thesis by (rule mm02b)
qed

lemma mm06: assumes "X <~ Y" "Y <~ Z" shows "X <~ Z" using assms by linarith

lemma assumes "finite Y" "X \<subseteq> Y" shows "card X - 1\<le> card Y - 1" using assms 
by (metis card_mono diff_le_mono)

lemma mm07: assumes "finite Y" "X \<subseteq> Y" "Y <~ Z" shows "X <~ Z" using assms card_mono diff_le_mono 
by (metis le_trans)

lemma mm07b: assumes "finite Z" "X <~ Y" "Y \<subseteq> Z" shows "X <~ Z" using assms card_mono diff_le_mono 
by (metis le_trans)

abbreviation "rotateLeft == rotate"
abbreviation "rotateRight n l == rotateLeft (size l - (n mod (size l))) l"
abbreviation "insertAt x l n == rotateRight n (x#(rotateLeft n l))"
(* for n in {0, ..., size l} inserts x in l so that it will have index n in the output*)
(* note that for other n, the behaviour is not guaranteed to be consistent with that *)
fun perm2 where
"perm2 [] = (%n. [])" | 
"perm2 (x#l) = (%n. insertAt x ((perm2 l) (n div (1+size l))) (n mod (1+size l)))"
(* for n in {0,..., fact(size l) - 1 }, 
perm2 l n gives all and only the possible permutations of l *)
abbreviation "takeAll pre list == map (nth list) (filterpositions2 pre list)"
abbreviation "subList l xl == map (nth l) (takeAll (%x. x \<le> size l) xl)"
abbreviation "insertRightOf2 x l n == (subList l (map nat [0..n])) @ [x] @ 
(subList l (map nat [n+1..size l - 1]))"
abbreviation "insertRightOf3 x l n == insertRightOf2 x l (Min {n, size l - 1})"
definition "insertRightOf x l n = sublist l {0..<1+n} @ [x] @ sublist l {n+1..< 1+size l}"
lemma "set (insertRightOf x l n) = set (sublist l {0..<1+n}) \<union> (set [x]) \<union> 
set (sublist l {n+1..<1+size l})" using insertRightOf_def 
by (metis append_assoc set_append)
lemma "set l1 \<union> set l2 = set (l1 @ l2)" by simp

lemma "sublist l {0..<1+n} @ (sublist l {1+n..<1+n+m}) = sublist l {0..<1+n+m}" 
using sublist_append sorry
lemma "set (sublist l {0..<1+(n::nat)}) \<union> 
set (sublist l {1+n..<1+size l}) = set (sublist l ({0..<1+(n::nat)}\<union>{0..<1+size l}))" sorry

(* 
fun perm where 
"perm [] = {}" | "perm (x#l) = 
{(n::nat, insertRightOf x (perm l,,(n div size l)) (n mod (size l)))| n . fact (size l) < n & n <= fact (1 + (size l))}
+* (perm l)"
*)

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

abbreviation "chosenAllocation N G bids random ==
hd (perm2
(takeAll (%x. x\<in>(winningAllocationsRel N (set G) bids)) (possibleAllocationsAlg3 N G))
random)"

lemma assumes "distinct list" shows "perm (permL list n) list" 
using assms permL_def sorry

abbreviation "resolvingBid N G bids random == tiebids (chosenAllocation N G bids random) N (set G)"
abbreviation "Vcga' N G R b == arg_max' (setsum (resolvingBid N G b R)) (set (Vcgas N G b))"
abbreviation "terminatingAuctionRel N G bids random == arg_max' (setsum (resolvingBid N G bids random))
(arg_max' (setsum bids) (possibleAllocationsRel N (set G)))"
abbreviation "vcga' N G bids random == the_elem 
(arg_max' (setsum (resolvingBid (N\<union>{auctioneer}) G (toFullBid (set G) bids) random))
(vcgas N (set G) bids))"
abbreviation "vcgp' N G b r n == alpha' N (set G) b n - 
(setsum (toFullBid (set G) b) (vcga' N G b r -- n))"

lemma nn13: "vcga' N G bids random = the_elem (terminatingAuctionRel (N\<union>{auctioneer}) G (toFullBid (set G) bids) random)"
by fast

lemma mm93: "terminatingAuctionRel N G bids random = (((arg_max' \<circ> setsum) (resolvingBid N G bids random))
\<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N (set G))" by auto

lemma mm83: assumes "l \<noteq> []" shows "perm2 l n \<noteq> []" using assms perm2_def 
by (metis all_partitions_list.cases list.distinct(1) perm2.simps(2) rotate_is_Nil_conv)

lemma mm84c: assumes "\<exists> n \<in> {0..<size l}. P (l!n)" shows "[n. n \<leftarrow> [0..<size l], P (l!n)] \<noteq> []"
using assms by auto
lemma mm84d: assumes "ll \<in> set (l::'a list)" shows "\<exists> n\<in> (nth l) -` (set l). ll=l!n"
using assms(1) by (metis in_set_conv_nth vimageI2)
lemma mm84e: assumes "ll \<in> set (l::'a list)" shows "\<exists> n. ll=l!n & n < size l & n >= 0"
using assms in_set_conv_nth by (metis le0)
lemma "(nth l) -` (set l) \<supseteq> {0..<size l}" using assms 
by fastforce
lemma assumes "l \<noteq> []" shows "(nth l) -` (set l) \<subseteq> {0..<1+size l}" using assms sorry

lemma mm84f: assumes "P -` {True} \<inter> set l \<noteq> {}" shows "\<exists> n \<in> {0..<size l}. P (l!n)" 
proof -
obtain ln where "P ln & ln \<in> set l" using assms by blast
then moreover obtain n where "ln=l!n & l \<noteq> [] & n <size l" 
using mm84e less_nat_zero_code list.size(3) by metis
ultimately show ?thesis by auto
qed

lemma mm84g: assumes "P -` {True} \<inter> set l \<noteq> {}" shows "[n. n \<leftarrow> [0..<size l], P (l!n)] \<noteq> []" 
using assms filterpositions2_def mm84f mm84c by metis
lemma mm94: "possibleAllocationsAlg2 N G = set (possibleAllocationsAlg3 N G)" by auto
lemma mm95: assumes "card N > 0" "distinct G" shows 
"winningAllocationsRel N (set G) bids \<subseteq> set (possibleAllocationsAlg3 N G)"
using assms mm94 lm03 by (smt lm70b map_eq_conv)
corollary mm96: assumes 
"N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows
"winningAllocationsRel N (set G) bids \<inter> set (possibleAllocationsAlg3 N G) \<noteq> {}"
using assms mm91 mm95 
proof -
let ?w=winningAllocationsRel let ?a=possibleAllocationsAlg3
let ?G="set G" have "card N > 0" using assms by (metis card_gt_0_iff)
then have "?w N ?G bids \<subseteq> set (?a N G)" using mm95 by (metis assms(3))
then show ?thesis using assms mm91 by blast
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
 
lemma mm98: "set (takeAll pre list) = ((nth list) ` set (filterpositions2 pre list))" by simp
lemma nn06: "(nth l) ` set ([n. n \<leftarrow> [0..<size l], (%x. x\<in>X) (l!n)]) \<subseteq> X\<inter>set l" by force
corollary nn06b: "(nth l)` set (filterpositions2 (%x.(x\<in>X)) l) \<subseteq> X \<inter>  set l" using filterpositions2_def nn06
proof -
have " filterpositions2 (%x.(x\<in>X)) l= [n. n \<leftarrow> [0..<size l], (%x. (x\<in>X)) (l!n)]" 
using filterpositions2_def by blast
moreover have "(nth l) ` set [n. n \<leftarrow> [0..<size l], (%x. x\<in>X) (l!n)] \<subseteq> X\<inter>set l" by (rule nn06) 
ultimately show ?thesis by presburger
qed
corollary nn06c: "set (takeAll (%x.(x\<in>X)) l) \<subseteq> X\<inter>set l" using nn06b mm98 by metis
lemma "(n\<in>{0..<N}) = ((n::nat) < N)" using atLeastLessThan_def atLeast0LessThan lessThan_iff by metis
lemma nn01: assumes "X \<subseteq> {0..<size list}" shows "(nth list)`X \<subseteq> set list" 
using assms atLeastLessThan_def atLeast0LessThan lessThan_iff by auto
lemma mm99: "set ([n. n \<leftarrow> [0..<size l], P (l!n)]) \<subseteq> {0..<size l}" by force
lemma mm99b: "set (filterpositions2 pre list) \<subseteq> {0..<size list}" using filterpositions2_def mm99 by metis
corollary nn02: "set (takeAll pre list) \<subseteq> set list" using mm99b mm98 nn01 by metis
corollary assumes "takeAll P list \<noteq> []" shows "set (takeAll P list) \<subseteq> set list"
using assms set_def mm98 filterpositions2_def sorry

lemma nn03: "set (insertAt x l n) = {x} \<union> set l" by simp
lemma nn04a: "\<forall>n. set (perm2 [] n) = set []" by simp
lemma nn04b: assumes "\<forall>n. (set (perm2 l n) = set l)" shows "set (perm2 (x#l) n) = {x} \<union> set l" 
using assms perm2_def nn03 by force
corollary nn04: "\<forall>n. set (perm2 l n) = set l" 
(* MC: this is weaker than saying (perm2 l n) is a permutation of l *) 
proof (induct l)
let ?P="%l. (\<forall>n. set (perm2 l n)=set l)"
show "?P []" using nn04a by force next let ?P="%l. (\<forall>n. set (perm2 l n)=set l)"
fix x fix l assume "?P l" then show "?P (x#l)" using nn04b by force
qed

corollary nn05a: "set (perm2 (takeAll (%x.(x\<in>X)) l) n) \<subseteq> X \<inter> set l" using nn06c nn04 by metis
corollary nn05b: assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows 
"perm2 (takeAll (%x. x \<in> winningAllocationsRel N (set G) bids) (possibleAllocationsAlg3 N G)) n \<noteq> []"
using assms mm83 mm84h by metis
corollary mm82: assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows 
"chosenAllocation N G bids random \<in> winningAllocationsRel N (set G) bids"
using assms nn05a nn05b hd_in_set in_mono Int_def Int_lower1 all_not_in_conv image_set nn04 nn06c set_empty subsetI subset_trans
proof -
let ?w=winningAllocationsRel let ?p=possibleAllocationsAlg3 let ?G="set G"
let ?X="?w N ?G bids" let ?l="perm2 (takeAll (%x.(x\<in>?X)) (?p N G)) random"
have "set ?l \<subseteq> ?X" using nn05a by fast
moreover have "?l \<noteq> []" using assms nn05b by blast
ultimately show ?thesis by (metis (lifting, no_types) hd_in_set in_mono)
qed

lemma assumes "distinct G" shows 
"possibleAllocationsAlg N (set G) = possibleAllocationsAlg3 N G" (is "?L=?R") 
using assms possible_allocations_alg_def injections_equiv all_partitions_paper_equiv_alg 
proof -
let ?i=injections_alg let ?p=all_partitions_alg let ?G="set G" 
let ?P=all_partitions_list
have "?R= map converse (concat [?i Y N. Y <- ?P G ])" by fast
have "set (?p ?G) \<subseteq> set (?P G)" using assms mm90 all_partitions_paper_equiv_alg sorry
have "?L = map converse (concat [?i Y N. Y <- ?p ?G ])" by simp
moreover have " ... = ?R" sorry
show ?thesis sorry
qed

lemma assumes "distinct G" shows 
"set (possibleAllocationsAlg N (set G)) \<supseteq> possibleAllocationsAlg2 N G" 
using assms possible_allocations_alg_def injections_equiv all_partitions_paper_equiv_alg 
sorry

corollary assumes "True" shows 
"takeAll (%x. x\<in>(winningAllocationsRel N (set G) bids)) (possibleAllocationsAlg N (set G)) \<noteq> []"
using mm84b
proof -
let ?w=winningAllocationsRel let ?P=possibleAllocationsAlg2 let ?p=possibleAllocationsRel
let ?G="set G"
(*
let ?l="?P N ?G" let ?P="%x. x \<in> ?w N ?G bids" 

have "{} \<noteq> ?w N ?G bids " sorry
have "card N > 0 & distinct G" sorry
moreover have "set ?l = ?p N ?G" using lm70b sorry  
then have "?P -` {True} \<noteq> {}" by blast
*)
show ?thesis sorry
qed

lemma assumes "card N > 0" "distinct G" "G \<noteq> []" shows 
"winningAllocationsRel N (set G) bids \<inter> possibleAllocationsAlg2 N G \<noteq> {}"
using assms lm70b lm03 sorry

lemma "chosenAllocation N G bids random \<in> winningAllocationsRel N (set G) bids" 
using assms mm83 mm84b sorry

lemma mm81: assumes
"N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}"
"aa \<in> (possibleAllocationsRel N (set G))-{chosenAllocation N G bids random}" shows 
"setsum (resolvingBid N G bids random) aa < setsum (resolvingBid N G bids random) (chosenAllocation N G bids random)"
using assms mm70d 
proof -
let ?a="chosenAllocation N G bids random" let ?p=possibleAllocationsRel let ?G="set G"
have "?a \<in> ?p N ?G" using mm82 assms lm03 set_rev_mp by auto
then show ?thesis using assms mm70d by blast
qed

(* MC: termination theorem *)
corollary mm92: assumes 
"N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" (*MC: why does this emerge only now? *) 
shows "terminatingAuctionRel N G bids random = {chosenAllocation N G bids random}"
using assms mm81 mm80 
proof -
let ?p=possibleAllocationsRel let ?G="set G" 
let ?X="arg_max' (proceeds bids) (?p N ?G)"
let ?a="chosenAllocation N G bids random" let ?b="resolvingBid N G bids random"
let ?f="setsum ?b" let ?ff="proceeds ?b" 
let ?t=terminatingAuctionRel
have "finite N" using assms by simp then 
have "finite (?p N ?G)" using assms lm59 by (metis List.finite_set)
then have "finite ?X" using assms by (metis finite_subset lm03)
moreover have "?a \<in> ?X" using mm82 assms by blast
moreover have "\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a" using assms mm81 by simp
ultimately have 
"finite ?X & ?a \<in> ?X & (\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a)" 
by fast 
moreover have "(finite ?X & ?a \<in> ?X & (\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a)) \<longrightarrow> arg_max' ?f ?X = {?a}"
by (rule mm80c)
ultimately have "{?a} = arg_max' ?f ?X" using mm80 by presburger
moreover have "... = ?t N G bids random" by fast
ultimately show ?thesis by presburger
qed

corollary mm92b: assumes "N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N"  
shows "vcga' N G bids random = chosenAllocation (N\<union>{auctioneer}) G (toFullBid (set G) bids) random" 
using assms mm92 nn13 by simp

corollary mm92c: assumes "N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga' N G bids random \<in> winningAllocationsRel (N \<union> {auctioneer}) (set G) (toFullBid (set G) bids)" 
using assms mm92b mm82 by simp

corollary nn14: assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows 
"Range (vcga' N G b r) partitions (set G)"
using assms mm92b mm82 lm47 lm03 
proof -
let ?p=possibleAllocationsRel let ?a="vcga' N G b r"
let ?w=winningAllocationsRel let ?B="toFullBid (set G) b"
have "?a \<in> ?w (N\<union>{auctioneer}) (set G) ?B" using assms mm92b mm82 lm47 lm03 by auto
moreover have "?w (N\<union>{auctioneer}) (set G) ?B \<subseteq> ?p (N\<union>{auctioneer}) (set G)" 
using assms mm92b mm82 lm47 lm03 by presburger
ultimately have "?a \<in> ?p (N\<union>{auctioneer}) (set G)" by fast
then show "Range ?a partitions (set G)" using lm47 by presburger
qed

lemma nn15: assumes "f,,,x \<noteq> {}" shows "x \<in> Domain f" using assms by fast
lemma nn15b: assumes "runiq f" "f,,,x \<noteq> {}" shows "f,,,x \<in> Range f" 
using assms nn15 lll82 by (metis eval_runiq_in_Range)

corollary lll81b: assumes "a \<in> possibleAllocationsRel N G" shows 
"runiq a & runiq (a\<inverse>) & (Range a) partitions G & Domain a \<subseteq> N" 
using assms  image_iff lll81 converse_converse by (metis lm47)

corollary lll81c: assumes "a \<in> winningAllocationsRel N G b" shows 
"runiq a & runiq (a\<inverse>) & (Range a) partitions G & Domain a \<subseteq> N" 
using assms lll81b by (metis (hide_lams, no_types) in_mono lm03)

lemma nn16: assumes "is_partition P"  
shows "(p1 \<in> P & p2 \<in> P & p1 \<inter> p2 \<noteq> {}) \<longrightarrow> p1 = p2" using assms is_partition_def by metis 

lemma nn17: assumes "runiq f" "runiq (f^-1)" "x1 \<in> Domain f" "x2 \<in> Domain f" "f,,x1 = f,,x2" shows "x1=x2"
using assms by (metis DomainE converse_iff l31)

abbreviation "evalRel3 R x == if (Range R\<in>Pow UNIV) then (\<Union> (R``{x})) else the_elem (R``{x})"
(*MC: does not solve my problem because the if condition automatically makes R have values of set type*)

lemma assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}"
"g \<in> ((vcga' N G b r),,,n1)" "g \<in> ((vcga' N G b r),,,n2)" shows "n1 = n2" 
using assms nn14 eval_rel_def 
proof -
let ?d=Domain let ?r=Range let ?a="vcga' N G b r" let ?P="Range ?a" 
let ?p1="?a,,,n1" let ?p2="?a,,,n2" have 
2: "n1 \<in> ?d ?a & n2\<in>?d ?a" using assms by fast moreover have 
0: "runiq ?a & runiq (?a^-1)" using assms lll81c mm92c by blast ultimately have 
3: "?p1=?a,,n1 & ?p2=?a,,n2" using lll82 by fast
have "is_partition ?P" using assms nn14 is_partition_of_def by blast
then have "(?p1 \<in> ?P & ?p2 \<in> ?P & ?p1 \<inter> ?p2 \<noteq> {}) \<longrightarrow> ?p1 = ?p2" using nn16 by blast
moreover have 
1: "?p1 \<in> ?r ?a & ?p2 \<in> ?r ?a" using nn15b assms 0 by fast
moreover have "?p1 \<inter> ?p2 \<noteq> {}" using assms by fast
ultimately have "?p1 = ?p2" by linarith
then show "n1 = n2" using 0 2 nn17 3 by fast
qed

lemma nn18: assumes "P partitions A" shows "\<Union> P = A \<and> is_partition P" using assms is_partition_of_def by metis

lemma assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}"
"g \<in> ((vcga' N G b r),,,m)" shows "g \<in> set G"
proof -
let ?r=Range let ?d=Domain let ?a="vcga' N G b r"
have "(?r ?a) partitions (set G)" using assms nn14 by presburger then have 
0: "\<Union> (?r ?a) = set G" using nn18 by blast
have "runiq ?a & runiq (?a^-1)" using assms lll81c mm92c by blast
then have "?a,,,m \<in> Range ?a" using assms nn15b by fast
thus ?thesis using 0 assms by blast 
qed

lemma nn19: "condition1 (toFullBid (set G) b) auctioneer" sorry
lemma lm61g: assumes "condition1 (toFullBid (set G) b) auctioneer" 
"auctioneer \<noteq> n" "finite N" "a \<in> winningAllocationsRel (N\<union>{auctioneer}) (set G) c"
shows "alpha' N (set G) b n >= setsum (toFullBid (set G) b) (a -- n)" using assms lm61b by blast
lemma assumes "N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" "seller\<noteq>n" shows "vcgp' N G b r n >= 0" using assms lm61g nn19 mm92c 
proof -
let ?w=winningAllocationsRel let ?N="N\<union>{auctioneer}" let ?a="vcga' N G b r"
let ?b="toFullBid (set G) b"
have "?a \<in> ?w ?N (set G) ?b" using assms mm92c by blast
then have "alpha' N (set G) b n >= setsum ?b (?a -- n)" using assms lm61g nn19 by blast
thus ?thesis by linarith
qed

theorem "\<forall> (b::bidvector). \<exists>! (a::allocation). a=vcga' N G b t" by fast
theorem "\<forall> (b::bidvector). \<exists>! (p::participant => price). p=vcgp' N G b t" by fast





























corollary mm92b: assumes "finite G" "finite N"  shows 
"(((arg_max' \<circ> setsum) (resolvingBid N G bids random))
\<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N G) 
= {chosenAllocation N G bids random}" using assms mm92 mm93 
by simp

corollary mm92c: assumes "finite G" "finite N"  shows 
"card ((((arg_max' \<circ> setsum) (resolvingBid N G bids random))
\<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N G)) 
= 1" using assms mm92b by auto

abbreviation "Tiebids N G bids random == tiebids (chosenAllocation N G bids random) N G"

corollary assumes "finite G" "finite N"  shows 
"card ((((arg_max' \<circ> setsum) (Tiebids N G bids random)) \<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N G)) 
= 1" using assms mm92c by fast

lemma "(arg_max' \<circ> setsum) bids (possibleAllocationsRel N G) = winningAllocationsRel N G bids"
by force

corollary assumes "finite G" "finite N" shows 
"card ((((arg_max' \<circ> setsum) (somebids)) \<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N G)) 
= 1" using assms mm92c sorry

(* tiebids (chosenAllocation N G bids random) N G *)

abbreviation "terminatingAuctionAlg N G bids random == argmax 
(proceeds (tiebids (hd (permL 
(takeAll (%x. x \<in> set (argmax (proceeds bids) (possibleAllocationsAlg3 N G))) (possibleAllocationsAlg3 N G)) 
(random::nat))) N (set G)))
(argmax (proceeds bids) (possibleAllocationsAlg3 N G))"


term "terminatingAuction N00 (set G00)"
value "arg_max' (%x. 1/x) {1,2::nat}"
value "possibleAllocationsAlg N00 (set G00)"
value "terminatingAuction N00 (set G00) (toFunction b00) 1"

abbreviation "indexof l x == hd (filterpositions2 (%y. x=y) l)"
notation indexof (infix "!-`" 75)
 
abbreviation "one N G random index == 
(% g n. (permL (sorted_list_of_set N) (random (index g))) !-` n + (card N)^(index g))"

abbreviation "tieBreakBidsSingle N G random index == % n g. 
(permL (sorted_list_of_set N) (random (index g))) !-` n + (card N)^(index g)" 
(* Gives, for each _single_ good, and each participant, a bid.
In such a way that the resulting proceeds are unique for each possible allocation
(as soon as index is injective)
*)

abbreviation "tieBreakBids N G random index == split (% n X.
setsum (tieBreakBidsSingle N G random index n) X
)"

value "proceeds (tieBreakBids {0::nat, 1} {10::nat,1} id id)"

abbreviation "tieBreaker N G random index == %X. arg_max' (proceeds (tieBreakBids N G random index))X "

lemma "!X. card (tieBreaker N G random index X) = 1" sorry

abbreviation "tieBreakerSeq N G random index == 
%n. (if (n=0) then (%X. tieBreaker N G random index X) else id)"

abbreviation "auction b t == geniter (%n. (t n) o (arg_max' (proceeds (b n))))" 
(* abbreviation "bidsequence b r == (%t. )" *)
(* abbreviation "auction B == geniter (%t. arg_max' (proceeds (B t)))" *)

lemma assumes "!n. !X. t n X <~ X" shows 
"card ((auction b t) 
(card (auction b t 0 X) - 1)
 X) - 1 <= 0" using mm05 assms 
proof -
let ?c=card let ?g=geniter let ?f="%n. (t n) o (arg_max' (proceeds (b n)))"
{
  fix n X
  have "arg_max' (proceeds (b n)) X \<subseteq> X" by auto
  moreover have "(t n) (arg_max' (proceeds (b n)) X) <~ arg_max' (proceeds (b n)) X" 
  using assms by fast
  moreover have "finite X" sorry
  ultimately
  have "((t n) o (arg_max' (proceeds (b n)))) X <~ X" using mm07b by auto
}
then have "\<forall>n. \<forall>X. ?f (n+1) X <~ X" by blast
then have "?c (?g ?f (?c (?g ?f 0 X) - 1) X) - 1 <= 0" using mm05 by fast
moreover have "auction b t=?g ?f" by fast
ultimately have "?c (auction b t (?c (auction b t 0 X) - 1) X) - 1 <= 0" by fast
then show ?thesis by fast
qed

lemma assumes "finite N" "finite G" 
(* "f 0=arg_max' (proceeds (b 0))" *) 
(* This only settles wdp, leaving the price determination completely undetermined *)
"!n. f (Suc n) = (%X. arg_max' (proceeds (b n)) (g (f n X)))"
"\<forall>Y. card (g Y) - 1 <= card Y - 2" shows
"EX n. card (prova f (possibleAllocationsRel N G) n) <= 0"
using assms prova_def prova_def mm02b sorry

notepad
begin
fix f N G fix n::nat fix b g
let ?X="possibleAllocationsRel N G"
have "prova f (possibleAllocationsRel N G) (n+2) = f (n+1) (prova f (possibleAllocationsRel N G) (n+1))"
using prova_def by auto
moreover have "... = arg_max' (proceeds (b n)) (g (f n ?X))" sorry
moreover have "g (f n ?X) \<subseteq> f n ?X" sorry
ultimately have "prova f ?X (n+2) \<subseteq> arg_max' (proceeds (b n)) (f n ?X)" sorry
end

lemma fixes f::"nat => nat" 
assumes "f 0 = m" "\<forall>n. (f n) - 1 >= f (n+1)" shows "f m <= 0" 
using assms nat_less_induct measure_induct_rule full_nat_induct infinite_descent nat_induct
lll20 sorry

lemma fixes f::"nat => nat" 
assumes "\<forall>n. ((f n) - 1 >= f (n+1) & f n > (0::nat))" shows "f ((f 0)+1) <= 2"
using assms infinite_descent sorry

lemma assumes "\<forall>(n::nat). (f n) - 1 >= f (n + (g n))" shows "EX n. f n = (0::nat)" 
using assms infinite_descent nat_induct sorry
term "Random_Sequence.not_random_dseq"
value "fst (Random.next (1,1))"

value "Random.pick [(1::natural,10::nat),(2,12),(3,13)] 3"

term "Limited_Sequence.single"

value "Random_Sequence.single (1::nat)"

end

