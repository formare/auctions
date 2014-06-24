theory a

imports Main Random Random_Sequence
g
"../Maximum"
"../Maskin3"
"../CombinatorialVickreyAuction"
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Permutations"
"~~/src/HOL/Library/Indicator_Function"
(* "~~/src/HOL/Library/DAList" *)

begin


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

lemma mm14: assumes "x \<in> X \<union> Y" shows "(X <| Y) x = chi X x" using assms toFunction_def 
mm13 sorry

corollary mm15: assumes "Z \<subseteq> X \<union> Y" shows "setsum (X <| Y) Z = setsum (chi X) Z" 
using assms mm14 setsum_cong by (smt in_mono)

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

lemma mm23: assumes "finite X" "finite Y" "card (X \<inter> Y) = card X" shows "X \<subseteq> Y" using assms 
by (metis Int_lower1 Int_lower2 card_seteq order_refl)

lemma assumes "finite X" "finite Y" "card X = card Y" shows "(card (X \<inter> Y)=card X) = (X = Y)"
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
abbreviation "partialCompletionOf bids pair == ((fst pair, snd pair), setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))"
abbreviation "linearCompletion bids N G == (partialCompletionOf bids) ` (N \<times> (Pow G - {{}}))"

corollary mm25: "snd (partialCompletionOf bids pair)=setsum bids (omega pair)" using mm24 by force

lemma mm26: "card (finestpart X) = card X" 
using finestpart_def by (metis (lifting) card_image inj_on_inverseI the_elem_eq)
corollary mm26b: "finestpart {} = {} & card \<circ> finestpart = card" using mm26 finestpart_def by fastforce

lemma mm40: "finite (finestpart X) = finite X" using assms finestpart_def mm26b by (metis card_eq_0_iff empty_is_image finite.simps mm26)
lemma "finite \<circ> finestpart = finite" using mm40 by fastforce

lemma mm27: assumes "finite  (finestpart (snd pair))" shows 
"card (omega pair) = card (finestpart (snd pair))" using assms by force

corollary assumes "finite (snd pair)" shows "card (omega pair) = card (snd pair)" 
using assms mm26 mm27 by (metis card_cartesian_product_singleton)

lemma mm29: assumes "X \<noteq> {}" shows "finestpart X \<noteq> {}" using assms finestpart_def by blast

lemma assumes "f \<in> allPartitionvalued" shows "{} \<notin> Range f" using assms by (metis lm22 no_empty_eq_class)

lemma mm30: assumes "{} \<notin> Range f" "runiq f" shows "is_partition (omega ` f)" 
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

lemma assumes "a \<in> allAllocations" shows "is_partition (omega ` a)" 
using assms is_partition_def sorry

lemma mm33: assumes "finite XX" "\<forall>X \<in> XX. finite X" "is_partition XX" shows 
"card (\<Union> XX) = setsum card XX" using assms is_partition_def card_Union_disjoint by fast

corollary mm33b: assumes "XX partitions X" "finite X" "finite XX" shows 
"card (\<Union> XX) = setsum card XX"
using assms mm33 by (metis is_partition_of_def lll41)

lemma assumes "inj_on g X" shows "setsum f (g`X) = setsum (f \<circ> g) X" using assms 
by (metis setsum.reindex)

lemma mm31: assumes "X \<noteq> Y" shows "{{x}| x. x \<in> X} \<noteq> {{x}| x. x \<in> Y}" using assms by auto

corollary mm31b: "inj_on finestpart UNIV" using mm31 ll64 by (metis (lifting, no_types) injI)

lemma mm32: assumes "{} \<notin> Range X" shows "inj_on omega X" using assms 
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

lemma mm34: "card ({x} \<times> Y) = card Y" by (metis card_cartesian_product_singleton)

lemma mm35: "card (omega pair)= card (snd pair)" using mm26 card_cartesian_product_singleton 
by metis

corollary mm35b: "card \<circ> omega = card \<circ> snd" using mm35 by fastforce

corollary mm37: assumes "{} \<notin> Range a" "\<forall> pair \<in> a. finite (snd pair)" "finite a" "runiq a" 
shows "card (pseudoAllocation a) = setsum (card \<circ> snd) a"
proof -
let ?P=pseudoAllocation let ?c=card
have "\<forall> pair \<in> a. finite (omega pair)" using mm40 assms by blast moreover
have "is_partition (omega ` a)" using assms mm30 by blast ultimately
have "?c (?P a) = setsum (?c \<circ> omega) a" using assms mm36 by blast
moreover have "... = setsum (?c \<circ> snd) a" using mm35b by metis
ultimately show ?thesis by presburger
qed

lemma mm38c: "inj_on fst P = inj_on snd (P^-1)" using  Pair_inject
by (smt converse.intros converseE inj_on_def surjective_pairing)

lemma mm39: assumes "runiq (a^-1)" shows "setsum (card \<circ> snd) a = setsum card (Range a)" 
using assms setsum.reindex lll33 mm38c converse_converse by (metis snd_eq_Range)

corollary mm46: assumes "runiq (a^-1)" "runiq a" "finite a" "{} \<notin> Range a" 
"\<forall> pair \<in> a. finite (snd pair)"
shows "card (pseudoAllocation a) = setsum card (Range a)" using assms mm39 mm37 by force

lemma mm47: "(\<forall> pair \<in> a. finite (snd pair)) = (\<forall> y \<in> Range a. finite y)" by fastforce

lemma mm41: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows
"\<forall> y \<in> Range a. finite y" using assms is_partition_of_def lm47 by (metis Union_upper rev_finite_subset)

lemma mm42: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "finite (Range a)" using assms lm47 
lm55 by (metis lm28)

lemma mm43: assumes "runiq f" shows "finite (Domain f) = finite f" 
using assms Domain_empty_iff card_eq_0_iff finite.emptyI lll34 by metis

corollary mm44: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "finite a"
using assms mm42 mm43 lm47 injections_def by (smt finite_converse mem_Collect_eq)

lemma mm45: assumes "XX \<in> allPartitionvalued" shows "{} \<notin> Range XX" using assms 
mem_Collect_eq no_empty_eq_class by auto

corollary mm45b: assumes "a \<in> possibleAllocationsRel N G" shows "{} \<notin> Range a" using assms mm45 
lm50 by blast

lemma assumes "a \<in> possibleAllocationsRel N G" shows "\<Union> Range a = G" using assms 
by (metis is_partition_of_def lm47)

corollary mm33c: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows 
"card G = setsum card (Range a)" using assms mm33b mm42 lm47 by (metis is_partition_of_def)

corollary mm48: assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "card (pseudoAllocation a) = card G"  
proof -
  have "{} \<notin> Range a" using assms mm45b by blast
  moreover have "\<forall> pair \<in> a. finite (snd pair)" using assms mm41 mm47 by metis
  moreover have "finite a" using assms mm44 by blast
  moreover have "runiq a" using assms by (metis (lifting) Int_lower1 in_mono lm19 mem_Collect_eq)
  moreover have "runiq (a^-1)" using assms by (metis (mono_tags) injections_def lm28b mem_Collect_eq)
  ultimately have "card (pseudoAllocation a) = setsum card (Range a)" using mm46 by blast
  moreover have "... = card G" using assms mm33c by metis
  ultimately show ?thesis by presburger
qed

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

lemma 
assumes "pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" 
"finite (pseudoAllocation aa)"
shows
"setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation a) - 
(setsum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation aa)) = 
card (pseudoAllocation a) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" using mm28 assms
by blast


lemma assumes "finite a" "N = Domain a" "G = \<Union> (snd ` a)" shows
"setsum (toFunction (linearCompletion bids N G)) a = setsum bids (pseudoallocation a)"
sorry

lemma assumes "!x. x \<in> Range a \<longrightarrow> finite x" "is_partition (Range a)" shows 
"card (pseudoAllocation a) = card (\<Union> Range a)"
using assms is_partition_def mm26 sorry

term "(bidMaximizedBy A00 N00 (set G00))"
term A00
value "Pow {} - {{}}"
value "linearCompletion (toFunction (bidMaximizedBy A00 N00 (set G00))) N00 (set G00)"

lemma mm08: assumes "finite X" shows 
"setsum f X <= card X * Max (Range (graph X f)) & 
setsum f X <= card X * Max (Range (graph X f))" using assms graph_def sorry

lemma mm09: assumes "finite a" "finite N" "finite G" shows 
"Min (Range (bidMaximizedBy a N G || a)) >= 1 &
Max (Range (bidMaximizedBy a N G || a)) <= 1" using assms Range_def paste_def
sorry

lemma assumes "runiq f" shows "Graph (toFunction f) \<supseteq> f" using assms Graph_def toFunction_def 
runiq_def sorry

lemma mm10: assumes "runiq f" "X \<subseteq> Domain f" shows 
"graph X (toFunction f) = (f||X)" using assms graph_def toFunction_def Outside_def 
restrict_def
by (smt Collect_mono Domain_mono Int_commute eval_runiq_rel ll37 ll41 ll81 restrict_ext restriction_is_subrel set_rev_mp subrel_runiq)

lemma mm11: assumes "runiq f" shows 
"graph (X \<inter> Domain f) (toFunction f) = (f||X)" using assms mm10 
by (metis Int_lower2 restriction_within_domain)

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

lemma "arg_max' f A \<subseteq> f -` {Max (f ` A)}"
using assms arg_max'_def Max_def image_def 
vimage_def 
by force

lemma m00: "arg_max' f A = A \<inter>{ x . f x = Max (f ` A) }"
using assms arg_max'_def Max_def image_def vimage_def
by auto

lemma "arg_max' f A = A \<inter> f -` {Max (f ` A)}"
using assms arg_max'_def Max_def image_def vimage_def
by force

value "arg_max' id {0::nat,2,3,1234}"

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

abbreviation "auction b t == geniter (%n. (t n) o (arg_max' (proceeds (b n))))"

lemma mm06: assumes "X <~ Y" "Y <~ Z" shows "X <~ Z" using assms by linarith

lemma assumes "finite Y" "X \<subseteq> Y" shows "card X - 1\<le> card Y - 1" using assms 
by (metis card_mono diff_le_mono)

lemma mm07: assumes "finite Y" "X \<subseteq> Y" "Y <~ Z" shows "X <~ Z" using assms card_mono diff_le_mono 
by (metis le_trans)

lemma mm07b: assumes "finite Z" "X <~ Y" "Y \<subseteq> Z" shows "X <~ Z" using assms card_mono diff_le_mono 
by (metis le_trans)

value "sublist [0::nat, 1, 2, 3] {0..<1}"
definition "insertRightOf x l n = sublist l {0..<1+n} @ [x] @ sublist l {n+1..< 1+size l}"
value "insertRightOf 44 [0::nat, 1, 2, 3] 2"
value "insertRightOf (44::nat) [] 0"
value "fact (12::nat)"

value "{0::nat ..<2}"

(* 
fun perm where 
"perm [] = {}" | "perm (x#l) = 
{(n::nat, insertRightOf x (perm l,,(n div size l)) (n mod (size l)))| n . fact (size l) < n & n <= fact (1 + (size l))}
+* (perm l)"
*)
term graph
value "(10::nat) div 6 "
fun perm::"'a list => (nat \<times> ('a list)) set" where 
"perm [] = {}" | "perm (x#l) = 
graph {fact (size l) ..< 1+fact (1 + (size l))}
(%n::nat. insertRightOf x (perm l,,(n div size l)) (n mod (size l)))
+* (perm l)"

value "perm [1::nat]``{1::nat}"
value "(id (1::nat := 3)) 4"

fun permL where (* associate to every n=1...(size l)! a unique permutation of l, 
parsing all and only the possible permutations (assuming distinct l)*)
"permL [] = (%n. [])"|
"permL (x#l) = (%n. 
if (fact (size l) < n & n <= fact (1 + (size l))) 
then
(insertRightOf x (permL l (n div size l)) (n mod (size l)))
else
(x # (permL l n))
)"

value "fact (5::nat)"

value "permL [0::nat,1,2,3,4,5] 79"
abbreviation "indexof l x == hd (filterpositions2 (%y. x=y) l)"
notation indexof (infix "!-`" 75)
value "[10::nat, 11, 12] !-` 12" 

abbreviation "one N G random index == 
(% g n. (permL (sorted_list_of_set N) (random (index g))) !-` n + (card N)^(index g))"

term "split (one {0::nat, 1} {10::nat, 11} id id)"

abbreviation "tieBreakBidsSingle N G random index == % n g. 
(permL (sorted_list_of_set N) (random (index g))) !-` n + (card N)^(index g)
" (* Gives, for each _single_ good, and each participant, a bid.
In such a way that the resulting proceeds are unique for each possible allocation
(as soon as index is injective)
*)

abbreviation "tieBreakBids N G random index == split (% n X.
setsum (tieBreakBidsSingle N G random index n) X
)"

value "proceeds (tieBreakBids {0::nat, 1} {10::nat,1} id id)"

abbreviation "tieBreaker N G random index == 
%X. arg_max' (proceeds (tieBreakBids N G random index))X "

lemma "!X. card (tieBreaker N G random index X) = 1" sorry

abbreviation "tieBreakerSeq N G random index== %n. (if (n=0) then (%X. tieBreaker N G random index X) else
id)"

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

