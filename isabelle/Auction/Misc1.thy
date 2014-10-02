theory Misc1

imports Main RelationProperties
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Indicator_Function"
Conditionally_Complete_Lattices
Maximum
Real_Vector_Spaces (*for ll57 lll62*)

begin

lemma nn56: "card X=1 = (X={the_elem X})" 
by (smt card_eq_SucD card_gt_0_imp_non_empty card_insert_disjoint finite.emptyI insert_absorb insert_not_empty the_elem_eq)
lemma nn57: assumes "card X=1" "X \<subseteq> Y" shows "Union X \<in> Y" using assms nn56 by (metis cSup_singleton insert_subset)

corollary ll52b: "(R outside X1) outside X2 = (R outside X2) outside X1" by (metis ll52 sup_commute)
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


lemma mm75f: assumes "f \<circ> g=id" shows "inj_on g UNIV" using assms 
by (metis inj_on_id inj_on_imageI2)

lemma mm74: assumes "inj_on f Y" "X \<subseteq> Y" shows "inj_on (image f) (Pow X)" using assms 
by (smt PowD inj_onI inj_on_image_eq_iff subset_inj_on)

lemma mm55m: "{Y. EX y. ((Y \<in> finestpart y) & (y \<in> Range a))} = 
\<Union> (finestpart ` (Range a))" by auto

lemma mm55l: "Range {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a} = 
{Y. EX y. ((Y \<in> finestpart y) & (y \<in> Range a))}" by auto

lemma mm55j: "{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a} = 
{(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a}"
using finestpart_def by fastforce

lemma mm55b: "{(fst pair, {y})| y. y \<in>  snd pair} = {fst pair} \<times> {{y}| y. y \<in> snd pair}" by fastforce

lemma mm71: "x \<in> X = ({x} \<in> finestpart X)" using finestpart_def by force

lemma nn43: "{(x,X)}-{(x,{})} = {x}\<times>({X}-{{}})" by blast

lemma nn11: assumes "\<Union> P = X" shows "P \<subseteq> Pow X" using assms by blast

lemma mm85: "arg_max' f {x} = {x}" using arg_max'_def by auto

lemma lm64: assumes "finite X" shows "set (sorted_list_of_set X)=X" using assms by simp

lemma lll23: assumes "finite A" shows "setsum f A = setsum f (A \<inter> B) + setsum f (A - B)" using 
assms by (metis DiffD2 Int_iff Un_Diff_Int Un_commute finite_Un setsum.union_inter_neutral)

lemma shows "(P||(Domain Q)) +* Q = Q" by (metis Int_lower2 ll41 ll56)

lemma lll77: assumes "Range P \<inter> (Range Q)={}" "runiq (P^-1)" "runiq (Q^-1)" shows "runiq ((P \<union> Q)^-1)"
using assms
by (metis Domain_converse converse_Un disj_Un_runiq)

lemma lll77b: assumes "Range P \<inter> (Range Q)={}" "runiq (P^-1)" "runiq (Q^-1)" 
shows "runiq ((P +* Q)^-1)"
using lll77 assms subrel_runiq by (metis converse_converse converse_subset_swap paste_sub_Un)

lemma lll71b: assumes "runiq P" shows "P\<inverse>``((Range P)-X) \<inter> ((P\<inverse>)``X) = {}"
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

lemma lll82: assumes "runiq (f::(('a \<times> ('b set)) set))" "x \<in> Domain f" shows "f,,x = f,,,x"
(* CL: Interesting: metis says that eval_rel_def is unused in the proof, but when I use it,
   the proof takes much longer (too long for me to wait) 
MC: I think this no longer applies? *) using assms Image_runiq_eq_eval cSup_singleton by metis

lemma lll79: assumes "\<Union> XX \<subseteq> X" "x \<in> XX" "x \<noteq> {}" shows "x \<inter> X \<noteq> {}" using assms by blast

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


lemma lm54: assumes "trivial X" shows "finite X" 
using assms finite.simps trivial_cases by metis

lemma lll86: assumes "X \<inter> Y={}" shows "R``X = (R outside Y)``X"
using assms Outside_def Image_def by blast

lemma lm02: "arg_max' f A = { x \<in> A . f x = Max (f ` A) }" using assms by simp

lemma lm04: "graph (X \<inter> Y) f \<subseteq> graph X f || Y" using graph_def assms restrict_def
by (smt Int_iff mem_Collect_eq restrict_ext subrelI)

lemma lm06: "graph X f = Graph f || X" using graph_def Graph_def restrict_def
by (smt inf_top.left_neutral  lm04 mem_Collect_eq prod.inject restrict_ext subsetI subset_antisym)

lemma lm05: "graph (X \<inter> Y) f = graph X f || Y" using lll02 lm06 by metis


lemma lll59: assumes "trivial Y" shows "runiq (X \<times> Y)" using assms 
runiq_def Image_subset ll84 trivial_subset by (metis ll83)

lemma "inj_on  (%a. ((fst a, fst (snd a)), snd (snd a))) UNIV" 
by (metis (lifting, mono_tags) Pair_fst_snd_eq Pair_inject injI)
lemma "(X={the_elem X}) = (card X=1)" 
by (smt card_empty card_eq_SucD card_insert_disjoint finite.emptyI insert_absorb insert_not_empty the_elem_eq)
lemma nn27: assumes "finite X" "x > Max X" shows "x \<notin> X" using assms Max.coboundedI by (metis leD)

lemma mm86: assumes "finite A" "A \<noteq> {}" shows "Max (f`A) \<in> f`A" 
using assms by (metis Max_in finite_imageI image_is_empty)

lemma "arg_max' f A \<subseteq> f -` {Max (f ` A)}" by force

lemma mm78: "arg_max' f A = A \<inter>{ x . f x = Max (f ` A) }" by auto

lemma nn60: "(x \<in> arg_max' f X) = (x \<in> X & f x = Max {f xx| xx. xx \<in> X})" using arg_max'_def 
by (smt Collect_cong Int_iff image_Collect_mem mem_Collect_eq mm78)

corollary nn59: assumes "finite g" shows "setsum f g = setsum f (g outside X) + (setsum f (g||X))" 
proof -
let ?A="g outside X" let ?B="g||X"
have "finite ?A" using assms(1) Outside_def by (metis finite_Diff)
moreover have "finite ?B" using assms(1) finite_Un outside_union_restrict by (metis)
moreover have "?A Int ?B = {}" unfolding Outside_def restrict_def by blast
ultimately show ?thesis using outside_union_restrict setsum.union_disjoint by metis
qed


lemma mm10: assumes "runiq f" "X \<subseteq> Domain f" shows 
"graph X (toFunction f) = (f||X)" using assms graph_def toFunction_def Outside_def 
restrict_def
by (smt Collect_mono Domain_mono Int_commute eval_runiq_rel ll37 ll41 ll81 restrict_ext restriction_is_subrel set_rev_mp subrel_runiq)

lemma mm11: assumes "runiq f" shows 
"graph (X \<inter> Domain f) (toFunction f) = (f||X)" using assms mm10 
by (metis Int_lower2 restriction_within_domain)

lemma mm65:"{(x, f x)| x. x \<in> X2} || X1 = {(x, f x)| x. x \<in> X2 \<inter> X1}" using graph_def lm05 by metis
lemma mm51: "Range -` {{}} = {{}}" by auto

lemma mm47: "(\<forall> pair \<in> a. finite (snd pair)) = (\<forall> y \<in> Range a. finite y)" by fastforce

lemma mm38c: "inj_on fst P = inj_on snd (P^-1)" using Pair_inject
by (smt converse.intros converseE inj_on_def surjective_pairing)

lemma mm39: assumes "runiq (a^-1)" shows "setsum (card \<circ> snd) a = setsum card (Range a)" 
using assms setsum.reindex lll33 mm38c converse_converse by (metis snd_eq_Range)

lemma mm29: assumes "X \<noteq> {}" shows "finestpart X \<noteq> {}" using assms finestpart_def by blast

lemma assumes "inj_on g X" shows "setsum f (g`X) = setsum (f \<circ> g) X" using assms by (metis setsum.reindex)

lemma mm31: assumes "X \<noteq> Y" shows "{{x}| x. x \<in> X} \<noteq> {{x}| x. x \<in> Y}" using assms by auto

corollary mm31b: "inj_on finestpart UNIV" using mm31 ll64 by (metis (lifting, no_types) injI)

lemma mm60: assumes "runiq R" "z \<in> R" shows "R,,(fst z) = snd z" 
using assms by (metis l31 surjective_pairing)

lemma mm59: assumes "runiq R" shows "setsum (toFunction R) (Domain R) = setsum snd R" using 
assms toFunction_def setsum_reindex_cong mm60 lll31 by (metis (no_types) fst_eq_Domain)

corollary mm59b: assumes "runiq (f||X)" shows "setsum (toFunction (f||X)) (X \<inter> Domain f) =
setsum snd (f||X)" using assms mm59 by (metis Int_commute ll41)
lemma "(R||X) `` X = R``X" using Int_absorb lll02 lll85 by metis
lemma mm61: assumes "x \<in> Domain (f||X)" shows "(f||X)``{x} = f``{x}" using assms
lll02 lll85 Int_empty_right Int_iff Int_insert_right_if1 ll41 by metis
lemma mm61b: assumes "x \<in> X \<inter> Domain f" "runiq (f||X)" shows "(f||X),,x = f,,x" 
using assms lll02 lll85 Int_empty_right Int_iff Int_insert_right_if1 eval_rel.simps by metis

lemma mm61c: assumes "runiq (f||X)" shows 
"setsum (toFunction (f||X)) (X \<inter> Domain f) = setsum (toFunction f) (X \<inter> Domain f)" 
using assms setsum_cong2 mm61b toFunction_def by metis
corollary mm59c: assumes "runiq (f||X)" shows 
"setsum (toFunction f) (X \<inter> Domain f) = setsum snd (f||X)" using assms mm59b mm61c by fastforce

corollary assumes "runiq (f||X)" shows "setsum (toFunction (f||X)) (X \<inter> Domain f) = setsum snd (f||X)" 
using assms mm59 ll41 Int_commute by metis
lemma mm26: "card (finestpart X) = card X" 
using finestpart_def by (metis (lifting) card_image inj_on_inverseI the_elem_eq)
corollary mm26b: "finestpart {} = {} & card \<circ> finestpart = card" using mm26 finestpart_def by fastforce

lemma mm40: "finite (finestpart X) = finite X" using assms finestpart_def mm26b by (metis card_eq_0_iff empty_is_image finite.simps mm26)
lemma "finite \<circ> finestpart = finite" using mm40 by fastforce

lemma mm43: assumes "runiq f" shows "finite (Domain f) = finite f" 
using assms Domain_empty_iff card_eq_0_iff finite.emptyI lll34 by metis


lemma mm24: "setsum ((curry f) x) Y = setsum f ({x} \<times> Y)"
proof -
let ?f="% y. (x, y)" let ?g="(curry f) x" let ?h=f
have "inj_on ?f Y" by (metis Pair_inject inj_onI) 
moreover have "{x} \<times> Y = ?f ` Y" by fast
moreover have "\<forall> y. y \<in> Y \<longrightarrow> ?g y = ?h (?f y)" by simp
ultimately show ?thesis using setsum_reindex_cong by metis
qed

lemma mm24b: "setsum (%y. f (x,y)) Y = setsum f ({x} \<times> Y)" using assms mm24 by (smt Sigma_cong curry_def setsum.cong)


corollary mm12: assumes "finite X" shows "setsum f X = setsum f (X-Y) + (setsum f (X \<inter> Y))" 
using assms Diff_iff IntD2 Un_Diff_Int finite_Un inf_commute setsum.union_inter_neutral by metis

corollary "(P +* Q) `` (X \<inter> (Domain Q))= Q``X"  by (metis Image_within_domain Int_commute ll50)

corollary mm19: assumes "X \<inter> Domain Q = {}" (is "X \<inter> ?dq={}") shows "(P +* Q) `` X = (P outside ?dq)`` X" 
using assms Diff_disjoint Image_empty Image_within_domain Un_Image sup_inf_absorb paste_def by metis

lemma mm20: assumes  "X \<inter> Y = {}"  shows "(P outside Y)``X=P``X"
using assms Outside_def by blast

corollary mm19b: assumes "X \<inter> Domain Q = {}" shows "(P +* Q) `` X = P``X" 
using assms mm19 mm20 by metis

lemma mm14b: "runiq ((X \<times> {x}) +* (Y \<times> {y}))" using assms lll59 trivial_singleton runiq_paste2 by metis


lemma mm23: assumes "finite X" "finite Y" "card (X \<inter> Y) = card X" shows "X \<subseteq> Y" using assms 
by (metis Int_lower1 Int_lower2 card_seteq order_refl)

lemma mm23b: assumes "finite X" "finite Y" "card X = card Y" shows "(card (X \<inter> Y)=card X) = (X = Y)"
using assms mm23 by (metis card_seteq le_iff_inf order_refl)

lemma "toFunction (Graph f)=f" (is "?L=_")
proof-{fix x have "?L x=f x" unfolding toFunction_def ll28 by metis}thus ?thesis by blast qed

lemma nn29: "R outside X \<subseteq> R" by (metis outside_union_restrict subset_Un_eq sup_left_idem)

lemma nn30a: "Range(f outside X) \<supseteq> (Range f)-(f``X)" using assms Outside_def by blast
lemma nn30b: assumes "runiq f" "runiq (f^-1)" shows "Range(f outside X) \<subseteq> (Range f)-(f``X)" using assms
Diff_triv lll78 lll85b Diff_iff ImageE Range_iff subsetI by smt
lemma nn30: assumes "runiq f" "runiq (f^-1)" shows "Range(f outside X) = (Range f)-(f``X)" 
using assms nn30a nn30b by (metis order_class.order.antisym)

lemma lm40: assumes "runiq (R^-1)" "runiq R" "X1 \<inter> X2 = {}" shows "R``X1 \<inter> (R``X2) = {}"
using assms by (metis disj_Domain_imp_disj_Image inf_assoc inf_bot_right)

lemma lm42: "(\<forall> x \<in> X. \<forall> y \<in> Y. x \<inter> y = {})=(\<Union> X \<inter> (\<Union> Y)={})" by blast

lemma "Domain ((a outside (X \<union> {i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) ) 
\<subseteq> Domain a - X \<union> {i}" using assms Outside_def by auto

lemma "(R - ((X\<union>{i})\<times>(Range R))) = (R outside X) outside {i}" using Outside_def 
by (metis ll52)

lemma "{(i, x)} - {(i,y)} = {i} \<times> ({x}-{y})" by fast

lemma lm44: "{x}-{y}={} = (x=y)" by auto

lemma assumes "R \<noteq> {}" "Domain R \<inter> X \<noteq> {}" shows "R``X \<noteq> {}" using assms
by (metis Image_outside_domain Int_commute)

lemma "R``{}={}" by (metis Image_empty)


lemma lm56: "R \<subseteq> (Domain R) \<times> (Range R)" by auto

lemma lm57: "(finite (Domain Q) & finite (Range Q)) = finite Q" using 
rev_finite_subset finite_SigmaI lm56 finite_Domain finite_Range by metis


lemma lll41: assumes "finite (\<Union> XX)" shows "\<forall>X \<in> XX. finite X" using assms
by (metis Union_upper finite_subset)














lemma ll57: (*repetition*) fixes a::real fixes b c shows "a*b - a*c=a*(b-c)"
using assms by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

lemma lll62: fixes a::real fixes b c shows "a*b - c*b=(a-c)*b" (*MC: repetition*)
using assms ll57 by (metis comm_semiring_1_class.normalizing_semiring_rules(7))

lemma lll92: assumes "xx \<in> X \<inter> (f^-1)``{f1,f2}" "f1 \<noteq> f2" "runiq f"
"\<forall>x \<in> X. (((f,,x=(f1::real)) \<longrightarrow> (g,,x=(g1 x))) & ((f,,x=f2) \<longrightarrow> (g,,x=g2 x)))" shows 
"g,,xx = (f,,xx - f1)*(g2 xx)/(f2-f1) + (f,,xx - f2)*(g1 xx)/(f1-f2)" 
proof -
  let ?fx="f,,xx" let ?h2="(?fx-f1)*(g2 xx)/(f2-f1)" let ?h1="(?fx-f2)*(g1 xx)/(f1-f2)" 
  let ?gx="g,,xx" have
  1: "?fx=f1 \<longrightarrow> ?gx=(g1 xx)" using assms by fast have
  2: "?fx=f2 \<longrightarrow> ?gx=(g2 xx)" using assms by fast  
  have "{xx} \<subseteq> (f^-1)``{f1,f2}" using assms by fast
  then have "f``{xx} \<subseteq> {f1,f2}" using assms(3) ll71b by metis
  then have 
  4: "f,,xx=f1 \<or> f,,xx=f2" using assms(3) by (metis Image_iff Image_singleton_iff Int_absorb1 
  Int_empty_left `{xx} \<subseteq> f\<inverse> \`\` {f1, f2}` converseD equals0D insert_subset l31 subset_insert)
  {
    assume "f,,xx=f1" then moreover have "?h2 = 0" by simp
    ultimately moreover have "?h1=g1 xx" using 1 assms by auto
    ultimately have "?gx=?h2 + ?h1" using 1 by simp 
  }
  then have
  3: "f,,xx=f1 \<longrightarrow> (?gx=?h2+?h1)" by fast
  {
    assume "f,,xx=f2" then moreover have "?h1 = 0" by simp
    ultimately moreover have "?h2=g2 xx" using 1 assms by auto
    ultimately have "?gx=?h2 + ?h1" using 2 by simp 
  }
  then have "?gx=?h2+?h1" using 3 4 by fast then show ?thesis by fast
qed

corollary lll92b: assumes "xx \<in> X \<inter> (f^-1)``{f1,f2}" "f1 \<noteq> f2" "runiq f"
"\<forall>x \<in> X. (((f,,x=(f1::real)) \<longrightarrow> (g,,x=(g1 x))) & ((f,,x=f2) \<longrightarrow> (g,,x=(%x. ((g1 x)+(g2 x))) x)))" 
shows "g,,xx = (f,,xx - f1)*(g2 xx)/(f2-f1) + (g1 xx)"
proof -
  let ?fx="f,,xx" let ?g1="g1 xx" let ?g2="g2 xx" let ?g="%x. (g1 x)+(g2 x)"
  have "\<forall> g2. ((xx \<in> X \<inter> (f^-1)``{f1,f2} &f1 \<noteq> f2 & runiq f &
  (\<forall>x \<in> X. (((f,,x=(f1::real)) \<longrightarrow> (g,,x=(g1 x))) & ((f,,x=f2) \<longrightarrow> (g,,x=g2 x))))) \<longrightarrow>
  g,,xx = (f,,xx - f1)*(g2 xx)/(f2-f1) + (f,,xx - f2)*(g1 xx)/(f1-f2))" using lll92 
  by smt
  then have 
  "((xx \<in> X \<inter> (f^-1)``{f1,f2} &f1 \<noteq> f2 & runiq f &
  (\<forall>x \<in> X. (((f,,x=(f1::real)) \<longrightarrow> (g,,x=(g1 x))) & ((f,,x=f2) \<longrightarrow> (g,,x=?g x))))) \<longrightarrow>
  g,,xx = (f,,xx - f1)*(?g xx)/(f2-f1) + (f,,xx - f2)*(g1 xx)/(f1-f2))"
  by fast
  then have "g,,xx = (?fx-f1)*(?g xx)/(f2-f1) + (?fx-f2)*?g1/(f1-f2)" using lll92 assms by blast
  moreover have "...=(?fx-f1)*((?g xx)/(f2-f1)) + (?fx-f2)*?g1/(f1-f2)" try0
  by auto
  moreover have "... = ?fx*((?g1+?g2)/(f2-f1)) - f1*(?g1+?g2)/(f2-f1) + (?fx-f2)*(?g1/(f1-f2))" 
  by (metis lll62 times_divide_eq_right) moreover have "... = 
  ?fx*?g1/(f2-f1) + ?fx*?g2/(f2-f1) - f1*(?g1+?g2)/(f2-f1) + (?fx-f2)*(?g1/(f1-f2))" by (metis 
  (hide_lams, mono_tags) add_divide_distrib comm_semiring_1_class.normalizing_semiring_rules(34) 
  times_divide_eq_right)
  moreover have "... = 
  ?fx*?g1/(f2-f1) + ?fx*?g2/(f2-f1) - f1*(?g1+?g2)/(f2-f1) + ?fx*(?g1/(f1-f2)) - 
  f2*(?g1/(f1-f2))" by (smt lll62)
  moreover have "... = ?fx*?g1/(f2-f1) + ?fx*?g1/(-(f2-f1)) + ?fx*?g2/(f2-f1) - f1*(?g1+?g2)/(f2-f1) - 
  f2*(?g1/(f1-f2))" by force
  moreover have "... = ?fx*?g1/(f2-f1) - ?fx*?g1/(f2-f1) + ?fx*?g2/(f2-f1) - f1*(?g1+?g2)/(f2-f1) - 
  f2*(?g1/(f1-f2))"
  by (metis (hide_lams, mono_tags) minus_divide_right minus_real_def)
  moreover have "... = ?fx*?g2/(f2-f1) - f1*((?g1+?g2)/(f2-f1)) - 
  f2*(?g1/(f1-f2))" by force
  moreover have "... = ?fx*?g2/(f2-f1) - (f1*?g1/(f2-f1) + f1*?g2/(f2-f1)) -
  f2*?g1/(f1-f2)"
  by (metis (hide_lams, no_types) add_divide_distrib comm_semiring_1_class.normalizing_semiring_rules(34) times_divide_eq_right)
  moreover have "... = ?fx*?g2/(f2-f1) - f1*?g1/(-(f1-f2)) - f1*?g2/(f2-f1) -
  f2*?g1/(f1-f2)" by force
  moreover have "... = ?fx*(?g2/(f2-f1)) + f1*(?g1/(f1-f2)) - f1*(?g2/(f2-f1)) -
  f2*(?g1/(f1-f2))" by (metis (hide_lams, mono_tags) diff_minus_eq_add minus_divide_right times_divide_eq_right)
  moreover have "... = ?fx*(?g2/(f2-f1)) + (f1-f2)*(?g1/(f1-f2)) - f1*(?g2/(f2-f1))" by (smt lll62)
  moreover have "... = (?fx-f1)*(?g2/(f2-f1)) + (f1-f2)*(?g1/(f1-f2))" by (smt lll62)
  moreover have "... = (?fx-f1)*?g2/(f2-f1) + ?g1*((f1-f2)/(f1-f2))" by simp
  moreover have "... = (?fx-f1)*?g2/(f2-f1) + ?g1*1" using assms by force
  ultimately show ?thesis by linarith
qed

lemma l31b: assumes "y \<in> f``{x}" "runiq f" shows "f,,x = y" using assms
by (metis Image_singleton_iff l31)


lemma mm84c: assumes "\<exists> n \<in> {0..<size l}. P (l!n)" shows "[n. n \<leftarrow> [0..<size l], P (l!n)] \<noteq> []"
using assms by auto
lemma mm84d: assumes "ll \<in> set (l::'a list)" shows "\<exists> n\<in> (nth l) -` (set l). ll=l!n"
using assms(1) by (metis in_set_conv_nth vimageI2)
lemma mm84e: assumes "ll \<in> set (l::'a list)" shows "\<exists> n. ll=l!n & n < size l & n >= 0"
using assms in_set_conv_nth by (metis le0)
lemma "(nth l) -` (set l) \<supseteq> {0..<size l}" using assms by fastforce
lemma mm84f: assumes "P -` {True} \<inter> set l \<noteq> {}" shows "\<exists> n \<in> {0..<size l}. P (l!n)" 
proof -
obtain ln where "P ln & ln \<in> set l" using assms by blast
then moreover obtain n where "ln=l!n & l \<noteq> [] & n <size l" 
using mm84e less_nat_zero_code list.size(3) by metis
ultimately show ?thesis by auto
qed

lemma mm84g: assumes "P -` {True} \<inter> set l \<noteq> {}" shows "[n. n \<leftarrow> [0..<size l], P (l!n)] \<noteq> []" 
using assms filterpositions2_def mm84f mm84c by metis

lemma nn06: "(nth l) ` set ([n. n \<leftarrow> [0..<size l], (%x. x\<in>X) (l!n)]) \<subseteq> X\<inter>set l" by force
corollary nn06b: "(nth l)` set (filterpositions2 (%x.(x\<in>X)) l) \<subseteq> X \<inter>  set l" using filterpositions2_def nn06
proof -
have " filterpositions2 (%x.(x\<in>X)) l= [n. n \<leftarrow> [0..<size l], (%x. (x\<in>X)) (l!n)]" 
using filterpositions2_def by blast
moreover have "(nth l) ` set [n. n \<leftarrow> [0..<size l], (%x. x\<in>X) (l!n)] \<subseteq> X\<inter>set l" by (rule nn06) 
ultimately show ?thesis by presburger
qed

lemma "(n\<in>{0..<N}) = ((n::nat) < N)" using atLeast0LessThan lessThan_iff by metis
lemma nn01: assumes "X \<subseteq> {0..<size list}" shows "(nth list)`X \<subseteq> set list" 
using assms atLeastLessThan_def atLeast0LessThan lessThan_iff by auto
lemma mm99: "set ([n. n \<leftarrow> [0..<size l], P (l!n)]) \<subseteq> {0..<size l}" by force
lemma mm99b: "set (filterpositions2 pre list) \<subseteq> {0..<size list}" using filterpositions2_def mm99 by metis

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

lemma mm55h: assumes "runiq a" shows "{(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a} = 
{(x, {y})| x y. y \<in> a,,x & x \<in> Domain a}" using assms Image_runiq_eq_eval 
by (metis (lifting, no_types) cSup_singleton)

lemma mm75: "X=\<Union> (finestpart X)" using ll64 by auto
lemma mm75b: "Union \<circ> finestpart = id" using finestpart_def mm75 by fastforce
lemma mm75c: "inj_on Union (finestpart ` UNIV)" using assms mm75b by (metis inj_on_id inj_on_imageI)





















subsection {* Computing all the permutations of a list *}
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

lemma mm83: assumes "l \<noteq> []" shows "perm2 l n \<noteq> []" 
using assms perm2_def perm2.simps(2) rotate_is_Nil_conv by (metis neq_Nil_conv)
lemma mm98: "set (takeAll pre list) = ((nth list) ` set (filterpositions2 pre list))" by simp

corollary nn06c: "set (takeAll (%x.(x\<in>X)) l) \<subseteq> X\<inter>set l" using nn06b mm98 by metis

corollary nn02: "set (takeAll pre list) \<subseteq> set list" using mm99b mm98 nn01 by metis
lemma nn03: "set (insertAt x l n) = {x} \<union> set l" by simp
lemma nn04a: "\<forall>n. set (perm2 [] n) = set []" by simp
lemma nn04b: assumes "\<forall>n. (set (perm2 l n) = set l)" shows "set (perm2 (x#l) n) = {x} \<union> set l" 
using assms perm2_def nn03 by force
corollary nn04: "\<forall>n. set (perm2 l n) = set l" 
(* MC: this is weaker than saying (perm2 l n) is a permutation of l *) 
proof (induct l)
let ?P="%l. (\<forall>n. set (perm2 l n)=set l)"
show "?P []" using nn04a by force next let ?P="%l. (\<forall>n. set (perm2 l n)=set l)"
fix x fix l assume "?P l" then show "?P (x#l)" by force
qed

corollary nn05a: "set (perm2 (takeAll (%x.(x\<in>X)) l) n) \<subseteq> X \<inter> set l" using nn06c nn04 by metis










abbreviation "toFunctionWithFallback R fallback == (% x. if (R``{x}={R,,x}) then (R,,x) else fallback)"
notation toFunctionWithFallback (infix "Else" 75)
abbreviation "setsum' R X == setsum (R Else 0) X"
abbreviation "setsum'' R X == setsum (toFunction R) (X \<inter> Domain R)"
abbreviation "setsum''' R X == setsum' R (X\<inter>Domain R)"
abbreviation "setsum'''' R X == setsum (%x. setsum id (R``{x})) X"

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
lemma "arg_max' (setsum' b) = (arg_max' \<circ> setsum') b" by simp

end
