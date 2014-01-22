theory f

imports 
(* "~~/src/HOL/Cardinals/Cardinal_Order_Relation_Base" *) 
(* SupInf *)
c 
Real 
(*
Set_Interval
Rings  
Quotient
Lifting
Transfer
*)
"~~/src/HOL/Library/Multiset"
"~~/src/HOL/Library/Function_Algebras" 
(*
"~~/src/HOL/Library/Cardinality"
"~~/src/HOL/Word/Misc_Typedef"
"~~/src/HOL/BNF/More_BNFs" Finite_Set
Nat 
*)
begin

(*
(* Multisets : stolen from More_BNFs.thy *)

(* The cardinal of a mutiset: this, and the following basic lemmas about it,
should eventually go into Multiset.thy *)
definition "mcard M \<equiv> setsum (count M) {a. count M a > 0}"

lemma mcard_emp[simp]: "mcard {#} = 0"
unfolding mcard_def by auto

lemma mcard_emp_iff[simp]: "mcard M = 0 \<longleftrightarrow> M = {#}"
unfolding mcard_def apply safe
  apply simp_all
  by (metis multi_count_eq zero_multiset.rep_eq)

lemma mcard_singl[simp]: "mcard {#a#} = Suc 0"
unfolding mcard_def by auto

lemma mcard_Plus[simp]: "mcard (M + N) = mcard M + mcard N"
proof-
  have "setsum (count M) {a. 0 < count M a + count N a} =
        setsum (count M) {a. a \<in># M}"
  apply(rule setsum_mono_zero_cong_right) by auto
  moreover
  have "setsum (count N) {a. 0 < count M a + count N a} =
        setsum (count N) {a. a \<in># N}"
  apply(rule setsum_mono_zero_cong_right) by auto
  ultimately show ?thesis
  unfolding mcard_def count_union[THEN ext] comm_monoid_add_class.setsum.F_fun_f by simp
qed

lemma setsum_gt_0_iff:
fixes f :: "'a \<Rightarrow> nat" assumes "finite A"
shows "setsum f A > 0 \<longleftrightarrow> (\<exists> a \<in> A. f a > 0)"
(is "?L \<longleftrightarrow> ?R")
proof-
  have "?L \<longleftrightarrow> \<not> setsum f A = 0" by fast
  also have "... \<longleftrightarrow> (\<exists> a \<in> A. f a \<noteq> 0)" using assms by simp
  also have "... \<longleftrightarrow> ?R" by simp
  finally show ?thesis .
qed













lemma lll21: shows "mcard M=size M" using mcard_def size_def by (metis set_of_def)
*)

lemma lll61: fixes x::real fixes y z 
shows "x/z-(y/z)=(x-y)/z" 
using assms by (metis diff_divide_distrib)

lemma lll64: fixes x::int shows "x-y+y=x" by force

lemma lll43: "(X2 \<times> {y}) outside X1 = (X2 - X1) \<times> {y}" using assms Outside_def 
by auto

lemma lll31: assumes "runiq P" shows "inj_on fst P" using assms 
runiq_def inj_on_def by (smt runiq_basic surjective_pairing)

lemma lll32: assumes "inj_on fst P" shows "runiq P" using assms 
inj_on_def by (metis (hide_lams, mono_tags) Pair_inject fst_conv runiq_basic)

lemma lll33: "runiq P=inj_on fst P" using lll31 lll32 by blast
(* Another characterization of runiq, reducing to lambda-functional injectivity *)

lemma lll34: assumes "runiq P" shows "card (Domain P) = card P" 
using assms lll33 card_image by (metis Domain_fst)

lemma lll22: shows "set_of M = (count M) -` {0<..}" using set_of_def by fast

lemma lll15:  fixes P and n :: nat
  assumes step: "\<And>n::nat. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n"
  shows "\<And>q. q \<le> n \<Longrightarrow> P q" using assms by (metis (full_types) infinite_descent)

lemma lll16: fixes P and n :: nat
  assumes step: "!m. (!l<m. P l) \<longrightarrow> P m"
shows "\<forall>q \<le> n. P q" 
using assms lll15 by blast

lemma lll17: fixes P and n::nat assumes "!m. m \<le> n \<longrightarrow> ((!l<m. P l) \<longrightarrow> P m)"
shows "\<forall>q \<le> n. P q" 
using assms lll16 by (metis leI le_trans order_refl)
(* using assms lll16 lll15 infinite_descent 
by (metis (hide_lams, mono_tags) le_neq_trans le_trans nat_le_linear) *)
(* by (metis le_less_trans le_neq_trans nat_le_linear) slower*)

lemma lll18: fixes P 
and n::nat assumes "!m. ((!l<m. P l) \<longrightarrow> P m)"
shows "\<forall>q \<le> n. P q" 
using lll15 assms by blast

lemma lll19: fixes P::"nat => bool" assumes "!m. ((!l<m. P l) \<longrightarrow> P m)"
shows "\<forall>q. P q" using lll15 assms by blast

lemma lll20: fixes P::"nat => bool" assumes "P (0::nat)" "\<forall>k::nat. (P k \<longrightarrow> P (Suc k))"
shows "\<forall>n::nat. (P n)" using assms by (metis nat_induct)

lemma lll05: fixes P Q y assumes 
"P^-1``{y} \<inter> (Q^-1``{y})={}" "finite (P^-1``{y})" "finite (Q^-1``{y})" 
shows "card ((P \<union> Q)^-1 ``{y})= card (P^-1``{y}) + card (Q^-1``{y})"
using assms converse_Un by (metis Un_Image card.union_inter_neutral empty_iff)

lemma lll08: fixes f assumes "finite {x. f x>0}" shows
"count (Abs_multiset f) = f" using assms 
by (metis (full_types) Abs_multiset_inverse mem_Collect_eq multiset_def)

lemma lll09: shows "Abs_multiset o count=id" using count_inverse by fastforce

lemma lll07: shows "(P \<inter> Q)``{x} = (P``{x} \<inter> (Q``{x}))" by fastforce

lemma assumes "P \<inter> Q={}" shows "P^-1 \<inter> Q^-1={}" using assms by fast

lemma lll00: shows "P||X = P outside (Domain P - X)" 
using Outside_def restrict_def by fastforce

lemma lll06a: shows "Domain (P outside X) \<inter> Domain (Q || X) \<subseteq> {}" using lll00 by 
(metis Diff_disjoint Domain_empty_iff Int_Diff inf_commute ll41 ll42 restrict_empty subset_empty)

lemma lll06b: shows "(P outside X) \<inter> (Q || X) = {}" using lll06a by fast

lemma lll11b: shows "P || (X \<inter> Y) \<subseteq> P||X & P outside (X \<union> Y) \<subseteq> P outside X" using 
Outside_def restrict_def Sigma_Un_distrib1 Un_upper1 inf_mono Diff_mono 
subset_refl by (metis (lifting) Sigma_mono inf_le1)

lemma lll06c: shows "(P outside (X \<union> Y)) \<inter> (Q || (X)) = {} & 
(P outside (X)) \<inter> (Q || (X \<inter> Z)) = {}
" using assms Outside_def restrict_def lll06b lll11b by fast

lemma lll11: shows "P || X \<subseteq> P||(X \<union> Y) & P outside X \<subseteq> P outside (X \<inter> Y)" 
using lll11b distrib_sup_le sup_idem inf_commute
by (smt le_inf_iff le_sup_iff subset_antisym sup.right_idem sup_commute)

lemma lll03: shows "P outside X \<subseteq> P outside (X \<inter> Domain P)" 
using Outside_def restrict_def lll11b by (smt Diff_Int Sigma_Int_distrib1 sup_ge1)

lemma lll01b: shows "P outside X \<subseteq> P || ((Domain P)-X)" 
using lll00 lll11 by (metis Int_commute ll41 outside_reduces_domain)

lemma lll01: shows "P outside X = P || (Domain P -X)" 
using Outside_def restrict_def  lll01b by fast

lemma lll02: shows "(P || X) || Y = P || (X \<inter> Y)" using lll00 ll52 
by (smt Int_commute Int_left_commute ll41 lll01 restriction_within_domain)

lemma lll04: shows "(P || X) outside Y = P || (X-Y)" using restrict_def
lll02 by (metis Diff_Compl double_complement ll42 lll00 lll01)

lemma lll06: shows "(P outside (X \<union> Y)) \<inter> (Q || (X \<inter> Z)) = {}" 
using lll06c by (metis (hide_lams, no_types) inf_commute lll02)

lemma ll57: (*repetition*) fixes a::real fixes b c shows "a*b - a*c=a*(b-c)"
using assms by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

lemma lll62: fixes a::real fixes b c shows "a*b - c*b=(a-c)*b"
using assms ll57 by (metis comm_semiring_1_class.normalizing_semiring_rules(7))

lemma ll44: fixes x::real fixes y z shows "x*(y + z)=x*y + x*z" 
by (metis comm_semiring_1_class.normalizing_semiring_rules(34))

notation paste (infix "+<" 75)

abbreviation prova (infix "--" 75) where "f -- x \<equiv> f outside {x}"

abbreviation ler_in where "ler_in r == (\<Union>x. ({x} \<times> (r x -` {True})))"
(* inverts in_rel *)

abbreviation DDomain
::"('a \<times> 'b) set => ('a multiset)"
where "DDomain R == Abs_multiset (% x. (card (R`` {x})))"

abbreviation RRange
::"('a \<times> 'b) set => ('b multiset)"
where "RRange R == Abs_multiset (% y. (card (R^-1 `` {y})))"
lemma lll26: "{y. card (P^-1``{y}) > 0} \<subseteq> Range P" by (metis (lifting) Domain_converse Image_within_domain' card_empty less_numeral_extra(3) mem_Collect_eq subsetI)
lemma lll24: fixes f::"'a => 'b" and g::"'b => 'c" and P shows 
"g`{f y|y::'a. P y} = (g o f)`{y|y::'a. P y}" by auto
lemma lll25: assumes "inj_on f X" shows "setsum f X = setsum id (f`X)" 
using assms by (metis setsum_reindex_id)
lemma lll27: "{y. (P^-1``{y}) \<noteq> {}} \<supseteq> Range P" using assms by fast
lemma lll28: assumes "\<forall>y. finite (P^-1``{y})" 
shows "{y. (P^-1``{y}) \<noteq> {}} = {y. card (P^-1``{y})>0}" using assms by auto
lemma lll29: assumes "\<forall>y. finite (P^-1``{y})" shows 
"{y. card (P^-1``{y}) > 0} = Range P" using assms lll26 lll27 lll28 
by (metis subset_antisym)

lemma assumes "finite X" shows 
"setsum g {f x| x. x\<in>X} = setsum (g o f) X" using assms lll24 
setsum_reindex_nonzero sorry

lemma lll30: fixes P assumes "finite P" shows "size (RRange P)=card P"
proof -
let ?R=RRange let ?p="?R P" let ?r=Range let ?d=Domain 
have "\<forall>y. P^-1``{y} \<subseteq> ?d P" by blast
moreover have 
1: "finite P" using assms(1) by fast
ultimately have 
2: "\<forall>y. finite (P^-1``{y})" using finite_Domain finite_subset by fast
let ?f="%y. (P \<inter> (?d P \<times> {y}))" let ?g="%y. (P^-1``{y})" let ?B="?f ` (?r P)"
{ 
  fix y
  have "P^-1``{y} \<subseteq> ?d P" by fast then have "finite (P^-1``{y})" using 1 
  by (metis finite_Domain finite_subset)
  have "(P^-1``{y}) \<times> {y} = P \<inter> (?d P \<times> {y})" by fast 
  then have "card (P \<inter> (?d P \<times> {y})) = card (P^-1``{y} \<times> {y})" by presburger
  also have "... = card (P^-1``{y}) * (card {y})" by (metis card_cartesian_product)
  moreover have "...=card (P^-1``{y})" by fastforce 
  ultimately have "card (P \<inter> (?d P \<times> {y})) = card (P^-1``{y})" by presburger
}
then have "\<forall>y. (card o ?f) y= (card o ?g) y" by simp
then have "\<forall>y\<in>(?r P). (((card o ?f) y) = (card o ?g) y)" by fast
moreover have "inj_on ?f (?r P)" using Range_def inj_on_def by blast
then moreover have "setsum card ?B = setsum (card o ?f) (?r P)" using setsum_reindex_cong
by fastforce
ultimately moreover have "setsum (card o ?f) (?r P) = setsum (card o ?g) (?r P)" 
by (smt setsum_cong2)
ultimately have "setsum card ?B = setsum (card o ?g) (?r P)" by presburger
moreover have "finite {yy. (%y. card (P^-1``{y})) yy > 0}" using 1
by (metis (full_types) finite_Range lll26 rev_finite_subset)
then moreover have "count (RRange P) = (%y. card (P^-1``{y}))" using lll08 lll09 by fast
moreover have "... = card o ?g" by fastforce
ultimately moreover have "size (RRange P)=
setsum (card o ?g) (set_of (RRange P))" using size_def by metis
ultimately moreover have "set_of (RRange P) = {y. (card o ?g) y>0}" 
using set_of_def by metis 
ultimately moreover have "... = Range P" using lll29 2 by metis
ultimately moreover have "size (RRange P) = setsum (card o ?g) (?r P)" using lll29 
by presburger
ultimately have "size (RRange P)=setsum card ?B" by presburger
moreover have "P = \<Union> ?B" by auto
moreover have "finite P" using 1 by fast
ultimately moreover have "finite ?B" using 1 by (smt finite_UnionD)
ultimately moreover have "\<forall>A\<in>?B. finite A" by blast
ultimately moreover have "(ALL A:?B. ALL B:?B. A \<noteq> B --> A Int B = {})"
by blast
ultimately moreover have "card (Union ?B) = setsum card ?B" using card_Union_disjoint
by fast
ultimately moreover have "... = size (RRange P)" by presburger
ultimately moreover have "size (RRange P)=card (\<Union> ?B)" by presburger
ultimately show "size (RRange P)=card P" by presburger

(*
moreover have "set_of (RRange P) \<subseteq> Range P" using set_of_def 
sorry
(* let ?C="{P \<inter> (?d P \<times> {y})| y. True}" *)
let ?C="{P \<inter> (?d P \<times> {y})| y. y\<in>UNIV}"
let ?CCC="{P \<inter> (?d P \<times> {y})| y. y\<in>(?r P)}"
have "?B = ?CCC" by blast
have "\<Union> ?CCC = P & P = \<Union> ?B" by auto
have "{P \<inter> (?d P \<times> {y})| y. y\<in>UNIV} - {P \<inter> (?d P \<times> {y})| y. y\<in>(?r P)}
\<subseteq> {P \<inter> (?d P \<times> {y})| y. y \<in> (UNIV - (?r P))}" 
by auto
moreover have "{P \<inter> (?d P \<times> {y})| y. y \<in> (UNIV - (?r P))} \<subseteq> {{}}" by fast
ultimately have "?C - ?CCC \<subseteq> {{}}" by simp
then have "(?C - ?CCC = {{}}) \<or> (?C - ?CCC = {})" by blast
moreover have "finite (?r P)" sorry
then moreover have "finite ?CCC" by fastforce
ultimately moreover have "finite ?C" by (smt finite.emptyI finite_Diff2 finite_insert)
moreover have "setsum card {{}}=0" by force 
moreover have "setsum card {}=0" by fastforce
ultimately moreover have "setsum card (?C - ?CCC)=0" by smt
ultimately have "finite ?C & setsum card (?C - ?CCC)=0" by blast
moreover have "?CCC \<subseteq> ?C" by blast
ultimately moreover have "setsum card ?C = setsum card (?C - ?CCC) + setsum card ?CCC" using setsum_subset_diff 
by fast
ultimately have "setsum card ?C = 0 + setsum card ?CCC" by presburger
have "\<forall>X\<in>(?C - ?CCC). card X=0" sorry
let ?CC="{?f y| y. y\<in>UNIV}" have "?C = ?CC" by fastforce
{ 
  fix y
  have "(P^-1``{y}) \<times> {y} = P \<inter> (?d P \<times> {y})" by fast 
  then have "card (P \<inter> (?d P \<times> {y})) = card (P^-1``{y} \<times> {y})" by presburger
  also have "... = card (P^-1``{y}) * (card {y})" by (metis card_cartesian_product)
  moreover have "...=card (P^-1``{y})" by fastforce 
  ultimately have "card (P \<inter> (?d P \<times> {y})) = card (P^-1``{y})" by presburger
}
then have "\<forall>y. card (P \<inter> (?d P \<times> {y}))= card (P^-1``{y})" by fast
then moreover have "(%y. card (P \<inter> (?d P \<times> {y}))) = (%y. card (P^-1``{y}))" by fast
moreover have "\<Union> ?C = P" by auto
moreover have "finite P" sorry 
ultimately moreover have "finite ?C" by (smt finite_UnionD)
ultimately moreover have "\<forall>A\<in>?C. finite A" by blast
ultimately moreover have "(ALL A:?C. ALL B:?C. A \<noteq> B --> A Int B = {})"
by blast
ultimately moreover have "card (Union ?C) = setsum card ?C" using card_Union_disjoint
by fast
ultimately moreover have "... = setsum card ?CC" by blast
ultimately have "... = setsum (card o ?f) UNIV" using lll24 sorry
ultimately have
  moreover have "card P = setsum (%y. card (P \<inter> (?d P \<times> {y}))) (?r P)"
  using 1 sorry
  ultimately have "card P = setsum (%y. card (P^-1``{y})) (?r P)" by presburger
  moreover have "... = size (RRange P)" using size_def set_of_def 
  sorry
let ?YY="finestpart (?r P)"
have "finite ?YY" sorry
moreover have "ALL A:?YY. finite A" using finestpart_def sorry
moreover have "(ALL A:?YY. ALL B:?YY. A \<noteq> B --> A Int B = {})" 
using finestpart_def sorry
ultimately have "card (Union ?YY) = setsum card ?YY" using card_Union_disjoint 
by blast
*)
qed

lemma lll12: "P``X \<subseteq> (P \<union> Q)``X" using assms by fast

lemma lll13: fixes P Q x assumes "P \<subseteq> Q" "finite (Q``{x})" shows 
"card (P``{x}) \<le> card (Q``{x})"
using assms card_mono lll12 by (metis subset_Un_eq)

lemma lll14: assumes "P \<subseteq> Q" "\<forall>y. finite (Q^-1``{y})" 
(* "finite {y. card (Q^-1``{y}) > 0}" *)
shows
"!y. (%y. (card (P^-1``{y}))) y \<le> (%y. (card (Q^-1``{y}))) y" 
using assms lll13 converse_subrel by metis

lemma lll35: fixes P Q y assumes "P \<subseteq> Q" 
"finite (Q^-1``{y})"
shows "card (P^-1 `` {y}) \<le> card (Q^-1``{y})"
using assms by (metis converse_subrel lll13)

lemma lll36: assumes "P \<subseteq> Q" 
"\<forall>y. finite (Q^-1``{y})" 
"finite {y. card (P^-1``{y}) > 0}"
"finite {y. card (Q^-1``{y}) > 0}"
shows "RRange P \<le> RRange Q" 
using assms lll35 lll08 mset_less_eqI by metis

lemma lll42: assumes "finite P" shows "finite {y. card (P^-1``{y})>0}"
using assms bot_nat_def finite_Range lll26
by (metis (full_types) finite_subset)

lemma lll41: assumes "finite (\<Union> XX)" shows "\<forall>X \<in> XX. finite X" using assms
by (metis Union_upper finite_subset)

lemma lll37: "\<Union> {P^-1 `` {y}|y. y\<in> Range P} = Domain P" by blast

lemma lll38: "P``{z} \<subseteq> Range P & P^-1``{z} \<subseteq> Domain P" by fast
(* unused? *)

lemma lll39: assumes "finite (Domain P)" shows "finite (P^-1``{y})" 
proof - 
  have "\<forall>y. P^-1``{y} \<subseteq> Domain P" by fast 
  thus ?thesis using finite_subset assms by fast
qed

lemma fixes y assumes "finite (P^-1``{y})" 
shows "y\<in>Range P = (card(P^-1``{y})>0)" using Range_def assms sorry

lift_definition onemember :: "'a => nat => 'a multiset" is 
"\<lambda>a n b. if b = a then n else 0" by (metis only1_in_multiset)

abbreviation onemember2 
::"'a => nat => 'a multiset"
where "onemember2 x n == RRange ({1..<n+1}\<times>{x})"

lemma ll00: shows "onemember x 1 = single x" by (metis onemember.abs_eq single.abs_eq)

lemma lll44: fixes n::nat shows "card {1..<n+1} =n" using assms 
by force
lemma lll45: "(X \<times> {yy})^-1``{yy}=X" by fast
lemma lll46: assumes "y \<noteq> yy" shows "(X \<times> {yy})^-1``{y}={}" using assms by fast

lemma lll47: assumes "card X=n" shows "card ((X \<times> {yy})^-1``{yy}) = 
 card (({1..<n+1} \<times> {yy})^-1``{yy})" using assms lll44 lll45 by metis

lemma lll48: assumes "y \<noteq> yy" shows "card ((X \<times> {yy})^-1``{y}) = 0
& 0 = card (({1..<n+1} \<times> {yy})^-1``{y})" using assms lll46 
by (metis card_empty)

lemma lll49: 
"(%y. card((X\<times>{yy})^-1``{y}))=(%y. card(({1..<(card X)+1}\<times>{yy})^-1``{y}))" 
using assms lll47 lll48 by metis

lemma lll51: "RRange (X \<times> {y})=onemember2 y (card X)" using lll49 by metis

lemma lll50: "(%y. card (({1..<n+1} \<times> {yy})^-1``{y})) = 
(\<lambda> b. if b = yy then n else 0)" using assms by (metis card_empty lll44 lll45 lll46)

lemma lll50b: "(%yy n y. card (({1..<n+1} \<times> {yy})^-1``{y})) = (%yy n b. if b = yy then n else 0)"
using lll50 by fast

lemma lll52: "onemember x n = onemember2 x n" 
proof -
let ?f="%a n b. if b = a then n else 0"
let ?g="%a n b. card (({1..<n+1} \<times> {a})^-1``{b})"
{
  fix a n
  have "?f a n = ?g a n" using lll50b by metis
  moreover have "Abs_multiset (?f a n) = onemember a n" by (metis onemember.abs_eq)
  moreover have "Abs_multiset (?g a n) = onemember2 a n" using lll08 lll09 by force
  ultimately have "onemember a n=onemember2 a n" by presburger
}
then show ?thesis by fast
qed

lemma assumes "finite X" "card X=n" shows "RRange (X \<times> {y})=onemember y n" 
using assms Image_def onemember.abs_eq single.abs_eq 
sorry

lemma lll10: fixes f::"'a => nat" fixes g::"'a => nat" 
assumes "finite {x. f x>0}" assumes "finite {x. g x > 0}" shows
"Abs_multiset f + (Abs_multiset g)=Abs_multiset (f+g)" using assms 
lll08 lll09 
proof -
  let ?a=Abs_multiset let ?c=count
  have "?c (?a f + (?a g))= ?c (?a f) + (?c (?a g))" using assms by fastforce
  moreover have "... = f + g" using assms lll08 by metis
  ultimately have "?a (f+g) = ?a (?c (?a f + (?a g)))" by simp
  also have "...=(?a f + (?a g))" by (metis count_inverse)
  ultimately show ?thesis by fastforce
qed


















section {*Maskin's 3*}

abbreviation pred0 where "pred0 (b::('a \<times> real) set) 
(P::(real multiset) => real) (f::(('a \<times> real) set) => real) ==
(setsum (%i. P (RRange (b -- i))) (Domain b) = f b)"

fun foo 
::"nat => (real (* could be real *) => real)"
where 
"foo (0::nat) = (%x. 1/(x+1))" |
"foo (Suc k) = (%x. (1-((Suc k)*((foo k) x)))/(x-k))"

lemma lll67: fixes x::real fixes k::nat assumes 
"x \<noteq> -1"
"x \<noteq> k"
"foo k x=1/(x+1)" shows 
"foo (Suc k) x = 1/(x+1)"
proof - 
let ?K="Suc k" have 
0: "x+1 \<noteq> 0 & x \<noteq> k" using assms(1,2) by auto then have 
"foo ?K x=((x+1)/(x+1)-(?K/(x+1)))/(x-k)" using foo_def assms(3) by auto
moreover have "(x+1)/(x+1)-(?K/(x+1))=(x+1-?K)/(x+1)" using lll61 by fast
ultimately have "foo ?K x = (x+1-?K)/(x+1)/(x-k)" by presburger
moreover have "...=(x-k)/(x+1)/(x-k)" 
by (metis ab_group_add_class.add_diff_cancel_left
comm_semiring_1_class.normalizing_semiring_rules(24) real_of_nat_Suc)
moreover have "...=1/(x+1)" using 0 by fastforce
ultimately show ?thesis by presburger
qed

corollary lll67b: 
fixes x::real 
(* assumes 
"x \<noteq> -1"*)
shows
"\<forall>k. (k<x \<longrightarrow> foo k x=1/(x+1)) \<longrightarrow> ((Suc k < x) \<longrightarrow> foo (Suc k) x=1/(x+1))" 
using lll67 by simp
(* by (metis One_nat_def Suc_eq_plus1 comm_semiring_1_class.normalizing_semiring_rules(24) divide_1 divide_zero foo.simps(1) foo.simps(2) real_of_nat_1 real_of_nat_Suc real_of_nat_zero zero_diff zero_neq_one) *)

corollary lll67c: fixes x::real fixes k::nat shows
"\<forall>k. k<x \<longrightarrow> foo k x=1/(x+1)" 
using assms lll67b nat_induct lll20
proof-
let ?p="%k. (k<x \<longrightarrow> (foo k x=1/(x+1)))"
  {
    fix P::"nat => bool" assume 
    23: "P=?p"
    then have "P (0::nat) & (!k::nat. (P k \<longrightarrow> P (Suc k)))" 
    using lll67b foo_def by force
    then have "!n::nat. (P n)" using nat_induct by auto
    then have "\<forall>n::nat. (?p n)" using 23 by fast
  }
  then have "\<forall>P::(nat => bool). P=?p \<longrightarrow> (\<forall>n::nat. ?p n)" by fast
  moreover have "?p=?p" by fast
  ultimately show "!n::nat. ?p n" by presburger
qed


abbreviation bar where "bar x k == foo k x"

lemma lll53: fixes b::"('a \<times> real) set" fixes P::"real multiset => real"
fixes b0::real fixes i1::'a fixes i2::'a
fixes m::"real multiset" fixes f::"('a \<times> real) set => real"
assumes 
"finite (Domain b)"
"i1 \<noteq> i2 & Domain b \<inter>{i1,i2}={}"
"pred0 ((Domain b \<union> {i1,i2}) \<times> {b0}) P f"
"size m=0"
shows "
(* \<forall>m. ((m \<le> RRange b & (size m)=(0::nat)) \<longrightarrow> *)
(P(m + (onemember2 b0 (card (Domain b)+1 - (0::nat))))=
(bar (card (Domain b)+1) (0::nat))*(f ((Domain b \<union> {i1,i2}) \<times> {b0})))" 
proof -
  let ?d=Domain let ?c=card  let ?o=onemember let ?o2=onemember2 let ?R=RRange
  let ?I12="{i1,i2}" let ?I="?d b" let ?n="?c ?I+1" let ?II="?I \<union> ?I12" 
  let ?B0="?II \<times> {b0}"
  let ?f="%i. P(?R(?B0--i))" let ?g="%i. P (?o2 b0 ?n)"
  have
  1: "finite ?II" using assms(1) by fast then have 
  2: "card ?II=?n+1" using assms(2) by auto
  have 
  10: "?d ?B0=?II" by fast
  {
    fix i  
    have "?B0 -- i = (?II-{i}) \<times> {b0}" by (metis lll43)
    then have "?R (?B0 -- i) = ?o2 b0 (card (?II-{i}))" using lll51 by metis
    moreover assume "i \<in> ?II"
    then moreover have "{i} \<subseteq> ?II & finite {i}" by auto
    then moreover have "card (?II-{i}) = (card ?II) - (1::nat)" 
    using 1 by (metis (full_types) calculation(2) card_Diff_singleton_if)
    ultimately have "?R (?B0 -- i) = ?o2 b0 ?n" using 2 by force
  }
  then have "\<And>x. x \<in> ?II \<Longrightarrow> ?f x = ?g x" by presburger
  then have "setsum ?f ?II = setsum ?g ?II" 
  using setsum_cong2 by force
  moreover have "... = (card ?II) * (P (?o2 b0 ?n))" 
  using setsum_constant by (metis real_eq_of_nat)
  ultimately have "(?n+1) * (P (?o2 b0 ?n))= setsum ?f ?II" using 2 by presburger
  moreover have "... = f ?B0" using assms(3) 10 by fastforce
  ultimately have "(f ?B0) = (real (?n+1)) * (P (?o2 b0 ?n))" by presburger
  moreover have "real (?n+1) \<noteq> 0" by simp
  ultimately have "(f ?B0)/(real (?n+1)) = P (?o2 b0 ?n)" by force
  moreover have "... = P(m+(?o2 b0 ?n))" using assms(4) by force
  ultimately have "P(m+(?o2 b0 (?n-(0::nat))))= (1/(?n+1)) * (f ?B0)" by force
  moreover have "bar ?n 0=1/(?n+1)" by auto
  ultimately show ?thesis by presburger
qed

abbreviation pred1 where 
(* Proof by induction on k *)
"pred1 (b::(('a \<times> real) set)) (b0::real) (i1::'a) (i2::'a) 
(f::(('a \<times> real) set) => real) (P::(real multiset) => real) (k::nat) 
== 
\<forall>m. (m \<le> RRange b & size m=k)\<longrightarrow> (P(m + onemember2 b0 (card (Domain b)+1-k))=
(bar (card (Domain b)+1) k)*f ((Domain b \<union> {i1,i2})\<times>{b0}))"

definition pred2 where "pred2 b (i1::'a) i2 (b0::real) X =
(\<forall> (m::real multiset). (
(m\<le>RRange b) \<longrightarrow> (\<exists> (J::'a set). 
(J \<subseteq> Domain b & ((Domain b \<union> {i1,i2})\<times>{b0}) +< (b||J) \<in> X & RRange(b||J)=m)
)))"

definition pred3 where 
"pred3 b (i1::'a) i2 (b0::real) X f = 
(\<forall> J. (((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b || J) \<in> X) \<longrightarrow> 
(f (((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b||J)) = f ((Domain b \<union> {i1,i2}) \<times> {b0})))"

definition pred22 where "pred22 B I1 I2 b0 X=
(\<forall> i2\<in>{I1,I2}. \<forall>i1\<in>{I1,I2} \<union> Domain B - {i2}. \<forall> b. 
b = B outside {i1,i2} \<longrightarrow> pred2 b i1 i2 b0 X)"

lemma lll55:
fixes X::"(('a \<times> real) set) set" fixes b b0 i1 i2 f P
assumes
(* "\<forall> (m::real multiset). (m \<le> RRange b) \<longrightarrow> (\<exists> (J::'a set) \<subseteq> Domain b. 
((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b || J) \<in> X & RRange (b || J) = m)" *)
"pred2 b (i1::'a) i2 (b0::real) X"
"finite b"
"\<forall> bb\<in>X. pred0 bb P f"
"i1 \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
shows "pred1 b b0 i1 i2 f P (0::nat)"
proof -   
  let ?d=Domain let ?I12="{i1, i2}" let ?I="?d b" let ?M="RRange b" 
  let ?II="?I \<union> ?I12" let ?n="card ?I+1" let ?B0="?II\<times>{b0}" let ?C="bar ?n"
  have
  11: "\<forall> (m::real multiset). (m \<le> RRange b) \<longrightarrow> (\<exists> (J::'a set) \<subseteq> Domain b. 
  ((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b || J) \<in> X & RRange (b || J) = m)" using
  assms(1) pred2_def by metis
  have "{#} \<le> ?M" by (metis less_le_not_le mset_less_empty_nonempty order_refl) 
  then obtain J0 where 
  10: "J0 \<subseteq> ?I & ?B0 +< (b||J0)\<in>X & RRange (b||J0)={#}"
  using 11 by presburger have 
  "finite (b||J0)" using assms(2) finite_subset restriction_is_subrel by metis
  then moreover have "size {#}=card (b||J0)" using 10 lll30 by fastforce
  ultimately have "b||J0={}" by fastforce then have "?B0 \<in> X" using 10 paste_def 
  by (metis Domain_empty outside_union_restrict restrict_empty) then
  have "pred0 ?B0 P f" using assms(3) by fast moreover have "finite ?II" by (metis 
  Un_insert_left assms(2) finite_Domain finite_insert sup_bot_left sup_commute)
  moreover have "i1 \<noteq> i2 & Domain b \<inter>{i1,i2}={}" using assms(4) by auto
  ultimately show ?thesis using lll53 by fast
qed

definition pred33 where "pred33 B I1 I2 b0 X f=
(\<forall> i2\<in>{I1,I2}. \<forall>i1\<in>{I1,I2} \<union> Domain B - {i2}. \<forall> b. 
b = B outside {i1,i2} \<longrightarrow> pred3 b i1 i2 b0 X f)"

lemma lll54: fixes X b fixes b0::real fixes i1::'a fixes i2 f P fixes k::nat 
assumes 
"finite b"
"i1 \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
"pred2 b i1 i2 b0 X"
(* "\<forall> m. (m \<le> RRange b) \<longrightarrow> (\<exists> J \<subseteq> Domain b. 
((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b || J) \<in> X & RRange (b || J) = m)"
*)
"runiq b"
"pred1 b b0 i1 i2 f P k"
"\<forall> bb\<in>X. pred0 bb P f"
"pred3 b i1 i2 b0 X f"
(* "\<forall> J. ((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b || J) \<in> X \<longrightarrow> 
f (((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b||J)) = f ((Domain b \<union> {i1,i2}) \<times> {b0})"*)
shows "pred1 b b0 i1 i2 f P (Suc k)" 
proof -
  let ?R1="% P y. (P^-1``{y})" let ?R="%P y. card (?R1 P y)" let ?u=runiq
  let ?d=Domain let ?I12="{i1, i2}"
  (* fix i1::'a fix i2::'a fix b0::real 
  fix b::"('a \<times> real) set" *)
  let ?I="?d b" 
  let ?M="RRange b" 
  let ?II="?I \<union> ?I12" 
  let ?n="card ?I+1" 
  let ?B0="?II\<times>{b0}" let ?C="bar ?n" have 
  26: "finite b" using assms(1) by fast 
  then moreover have "finite ?I" by (metis finite_Domain)
  then moreover have "finite ?II & ?I \<subseteq> ?II" by blast 
  moreover have
  "i1 \<noteq> i2 & {i1, i2}\<inter>?I={}" using assms(2) by fast
  ultimately have 
  16: "?d ?B0=?II & finite ?II & ?I \<subseteq> ?II & card ?II=?n+1 & {i1, i2} \<inter> ?I={}" 
  by auto then have 
  27: "finite ?B0" by fast have
  0: "\<forall> m. (m \<le> ?M) \<longrightarrow> (\<exists> J \<subseteq> ?I. ?B0 +< (b || J) \<in> X & RRange (b || J) = m)"
  (* Closure property for X *)
  using assms(3) pred2_def by metis
  let ?g="% bb i. (P (RRange (bb -- i)))"
  have
  2: "\<forall> bb\<in>X. pred0 bb P f" using assms(6) by fastforce
  let ?pred="pred1 b b0 i1 i2 f P "
  (* "% k. \<forall>m. ((m \<le> ?M & size m=k)\<longrightarrow> P(m + onemember2 b0 (?n-k))=(?C k)*(f ?B0))" *)
  have
  18: "\<forall> J. ?B0 +< (b || J) \<in> X \<longrightarrow> f (?B0 +< (b||J)) = f ?B0"
  (* f behaves like max, at least on X *)
  using assms(7) pred3_def by metis
  have
  4: "?pred k" (* inductive hypothesis *) using assms(5) by fast
  {
    fix m assume 
    7: "m \<le> ?M & size m=k+1" then obtain J where 
    1: "J \<subseteq> ?I & ?B0 +< (b || J) \<in> X & RRange (b || J) =m"
    using 0 by presburger 
    let ?bb="?B0 +< (b || J)" 
    have "?B0 outside J \<subseteq> ?B0" using Outside_def
    restrict_def  by blast
    moreover have "(\<forall>X. (?B0 || X \<subseteq> ?B0))" using
    restrict_def by blast
    ultimately have "finite (?B0 outside J) 
    & (\<forall>X. finite (?B0 || X))" using 27 by (metis finite_subset)
    then have 
    25: "finite (?B0 outside J) & finite {x. (?R (?B0 outside J)) x >0}
    & (\<forall>X. finite(?B0||X) & finite{x. (?R (?B0||X)) x>0})" using lll42 by blast
    have "finite (b||J)" using 26 by (metis finite_subset restriction_is_subrel)
    then moreover have "card (b||J)=k+1" using 1 7 lll30 by metis
    moreover have 
    28: "?u b" using assms(4) by fast
    then moreover have "?u (b||J)" by (metis (full_types) restriction_is_subrel subrel_runiq)
    moreover have 
    24: "?d (b||J) = J" using 1 by (metis Int_absorb1 ll41)
    ultimately have 
    "finite (b||J) & finite b & ?u b & card J=k+1 & card (b||J)=k+1" 
    using lll34 26 by metis
    then have 
    12: "finite (b||J) & card J=k+1 & card (b||J)=k+1 & ?II-J \<noteq> {}" 
    using 1 16 by fast have 
    17: "finite J & J \<subseteq> ?II" using 1 16 rev_finite_subset by auto
    then have 
    11: "finite (Domain (b||J))" by (metis finite_Int ll41)
    have "?bb=?B0 outside (?d (b || J)) \<union> (b || J)" by (metis paste_def)
    moreover have "... = ?B0 outside J \<union> (b || J)" using 1 by (smt Int_absorb1 ll41)
    ultimately have 
    9: "?bb = (?B0 outside J) \<union> (b || J)" by presburger
    (*
    {
      fix i have "?bb -- i = (?B0 outside J) -- i \<union> ((b || J) -- i)" using 9 ll51 by metis
      moreover have "... = (?B0 outside (J \<union> {i})) \<union> ((b || J) -- i)" using ll52 by metis
      ultimately have "?bb -- i = (?B0 outside (J \<union> {i})) \<union> (b || (J-{i}))" using lll04
      by blast
    }
    then have "\<forall>i. ?bb -- i=(?B0 outside (J \<union> {i})) \<union> (b||(J-{i}))" by fastforce 
    *)
    let ?h="%i. P(m+onemember2 b0 (?n-(k+1)))"

    have 
    6: "\<forall>i. ((i \<in> (?II - J)) \<longrightarrow> (((?g ?bb) i) = (?h i)))"
    (*{*)
    proof 
      fix i
      { 
        fix y::real have "(?B0 outside (J \<union> {i}))^-1``{y} \<inter> ((b || (J \<inter> J))^-1``{y})={}"
        using lll06 by fast      
        also have "(b||J)^-1``{y} \<subseteq> Domain (b||J)" by fast 
        then also have "finite ((b||J)^-1``{y})" using 11 by (metis finite_subset)      
        moreover have "(?B0 outside (J \<union> {i}))^-1``{y} \<subseteq> ?d (?B0 outside (J \<union> {i}))" 
        using Outside_def outside_reduces_domain Image_def by fast
        then moreover have "((?B0 outside (J \<union> {i}))^-1``{y}) \<subseteq> (?d ?B0) - (J \<union> {i})" 
        using outside_reduces_domain by metis
        then moreover have "((?B0 outside (J \<union> {i}))^-1``{y}) \<subseteq> ?II - (J \<union> {i})" by blast
        moreover have "finite (?II - (J \<union> {i}))" using 16 by fast
        ultimately moreover have "finite ((?B0 outside (J \<union> {i}))^-1``{y})" by (smt rev_finite_subset)
        ultimately have "(?B0 outside (J \<union> {i}))^-1``{y} \<inter> ((b || (J \<inter> J))^-1``{y})={}
        & finite ((b||J)^-1``{y}) &
        finite ((?B0 outside (J \<union> {i}))^-1``{y})" by fast
      } 
      then have
      10: "\<forall>y. 
      (?B0 outside (J \<union> {i}))^-1``{y} \<inter> ((b || (J \<inter> J))^-1``{y})={} & 
      finite ((?B0 outside (J \<union> {i}))^-1``{y}) & finite ((b || J)^-1``{y})" by presburger
      show "(i \<in> (?II - J)) \<longrightarrow> ((?g ?bb) i=(?h i))"
      proof 
        assume 
        3: "i \<in> ?II - J"   
        have "?B0 outside (J \<union> {i}) = (?II-(J \<union> {i}))\<times>{b0}" using lll43 by metis
        then moreover have "RRange (?B0 outside (J \<union> {i}))=onemember2 b0 (card (?II-(J \<union> {i})))" 
        using lll51 by metis
        moreover have "i \<in> ?II-J & J \<union> {i} \<subseteq> ?II & finite (J \<union> {i})" 
        using 3 17 by blast
        ultimately moreover have "card (?II-(J \<union> {i}))=?n+1 - card (J \<union> {i})" 
        using 16 card_Diff_subset by metis
        ultimately moreover have "...=?n+1 - (k+2)" using 12 by simp
        ultimately have 
        19: "RRange (?B0 outside (J \<union> {i}))=onemember2 b0 (?n+1-(k+2))" by presburger  
        have "?bb -- i = (?B0 outside J) -- i \<union> ((b || J) -- i)" 
        using 9 ll51 by metis
        moreover have "... = (?B0 outside (J \<union> {i})) \<union> ((b || J) -- i)" 
        using ll52 by metis
        moreover have "... = (?B0 outside (J \<union> {i})) \<union> (b || (J-{i}))" using lll04
        by blast
        ultimately have "?bb -- i = (?B0 outside (J \<union> {i})) \<union> (b || J)" using 3 by force
        moreover have "?R (?B0 outside (J \<union> {i}) \<union> (b||J)) = 
        (?R (?B0 outside (J \<union> {i}))) + (?R (b||J))" using lll05 10 by fastforce
        moreover have "finite {x. (?R (b||J)) x > 0}" 
        using restriction_is_subrel lll42 finite_subset 26 by metis
        moreover have "finite {x. (?R (?B0 outside (J \<union> {i}))) x > 0}"
        using restriction_is_subrel lll42 finite_subset 27 lll01 by metis
        ultimately moreover have "RRange (?B0 outside (J \<union> {i}) \<union> (b || J)) = 
        RRange (?B0 outside (J \<union> {i})) + (RRange (b||J))" using lll10 by metis
        ultimately have 
        "P (RRange (?bb -- i)) = P ((RRange (?B0 outside (J \<union> {i}))) + m)" 
        using 1 by presburger 
        also have "... = P(m+(RRange (?B0 outside (J \<union> {i}))))" using add_commute by metis
        also have "... = P(m+(onemember2 b0 (?n + 1 - (k+2))))" using 19 by presburger
        ultimately show "(?g ?bb) i=(?h i)" by force  
      qed
    qed 
    (*}*)
  
    have 
    5: "\<forall>i::'a. ((i\<in>J) \<longrightarrow> ((?g ?bb) i = ((%j. (?C k)*(f ?B0)) i)))" using 4 2
    proof -
      {
        fix i::'a  
        have "b||(J-{i}) \<subseteq> b||J" by (metis Un_Diff_Int lll11)
        moreover have "\<forall>y. finite ((b||J)^-1``{y})" using lll39 17 24 by metis
        moreover have "finite {y. card ((b||J)^-1``{y}) > 0}" using lll42 by (metis 12)
        ultimately moreover have "finite {y. card ((b||(J-{i}))^-1``{y}) > 0}"
        using lll42 by (metis (full_types) 12 finite_subset)
        ultimately have 
        8: "b||(J-{i}) \<subseteq> b||J & RRange (b||(J-{i})) \<le> RRange (b||J)" using lll36 by blast
        assume 
        13: "i \<in> J"  
        have "?B0 outside J = (?II-J)\<times>{b0}" using lll43 by metis
        then have "RRange (?B0 outside J)=onemember2 b0 (card (?II-J))" using lll51 by metis
        moreover have "card (?II-J)=?n+1 - (k+1)" using 12 16 17 card_Diff_subset by metis
        ultimately have 
        23: "RRange (?B0 outside J)=onemember2 b0 (?n-k)" by fastforce
        have "?bb -- i = (?B0 outside J) -- i \<union> ((b || J) -- i)" 
        using 9 ll51 by metis
        moreover have "... = (?B0 outside (J \<union> {i})) \<union> ((b || J) -- i)" 
        using ll52 by metis
        moreover have "... = (?B0 outside (J \<union> {i})) \<union> (b || (J-{i}))" 
        using lll04 by blast
        ultimately have "?bb -- i = (?B0 outside J) \<union> (b||(J-{i}))" 
        using 13 inf_sup_aci(5) insert_absorb insert_is_Un by smt
        moreover have "?d (?B0 outside J) \<inter> J={}" 
        using outside_reduces_domain by fast
        moreover have "?d (b||(J-{i})) \<subseteq> J-{i}" using ll41 Int_lower2 by (metis)
        ultimately moreover have 
        "\<forall>y. (?B0 outside J)^-1``{y} \<inter> ((b || (J-{i}))^-1``{y})={}" by blast
        moreover have "\<forall>y. finite ((?B0 outside J)^-1``{y})" 
        using lll39 finite_Domain 25 by smt
        moreover have "\<forall>y. finite ((b || (J-{i}))^-1``{y})" 
        using finite_subset lll39 11 Domain_mono by (metis 8)
        ultimately moreover have "?R ((?B0 outside J) \<union> (b||(J-{i}))) = 
        (?R (?B0 outside (J))) + (?R (b||(J-{i})))" using lll05 by fastforce
        moreover have "finite {x. (?R (b||(J-{i}))) x > 0}"
        using restriction_is_subrel lll42 finite_subset 26 by metis
        moreover have "finite {x. (?R (?B0 outside J)) x > 0}" using 25 by force 
        ultimately have 
        14: "(?g ?bb) i = P(RRange (?B0 outside J) + (RRange (b||(J-{i}))))"
        using lll10 by metis
        have "(?g ?bb) i = ((%j. (?C k)*(f ?B0)) i)"
        proof -    
          have "finite (b||(J-{i}))" using 26 finite_subset restriction_is_subrel by metis
          moreover have "?u (b||(J-{i}))" using 28 by (metis restriction_is_subrel subrel_runiq)
          moreover have "?d (b||(J-{i}))=?I \<inter> (J-{i})" 
          using ll41 by metis
          moreover have "... = J - {i}" using 1 by fast
          ultimately moreover have "?d (b||(J-{i}))=J-{i}" by presburger
          ultimately moreover have "size (RRange (b||(J-{i})))= card (b||(J-{i}))" 
          using lll30 by fast
          ultimately moreover have "... = card (J-{i})" using lll34 by metis
          moreover have "...=k" 
          using 12 13 17 add_diff_cancel_left' card_Diff_singleton_if nat_add_commute by force
          ultimately
          have "size (RRange (b||(J-{i}))) = k" using 7 1 13 by presburger (*MC: here I need runiq b*)
          moreover have "RRange (b||(J-{i})) \<le> ?M" using 7 1 8 by force
          ultimately have "P(RRange (b||(J-{i})) + onemember2 b0 (?n-k))=
          (?C k)*(f ?B0)" using 4 by blast
          moreover have "RRange (?B0 outside J)=onemember2 b0 (?n-k)" 
          using 23 by fastforce
          ultimately have 
          "(?C k)*(f ?B0) = P(RRange (?B0 outside J) + (RRange (b||(J-{i}))))" 
          using add_commute by metis
          also have "... = (?g ?bb) i" using 14 by presburger
          finally have "(%i. (?C k)*(f ?B0)) i = (?g ?bb) i" by fastforce
          thus ?thesis by presburger
        qed
      }
      thus ?thesis by fastforce
    qed

    have "?d ?B0 = ?II" by auto then
    have "?d ?bb = ?II" using paste_def 1 by (smt 
    Int_absorb1 Un_insert_right insert_is_Un ll41 ll54 paste_Domain sup.commute)
    then have "f ?bb = setsum (?g ?bb) ?II" using 1 2 by fastforce
    moreover have "... = setsum (?g ?bb) (?II - J) + setsum (?g ?bb) J" 
    using setsum_subset_diff 1 17 16 by auto
    moreover have "... = setsum (?g ?bb) (?II - J)
    +(\<Sum> i\<in>J. ((?C k)*(f ?B0)))" using 5 by fastforce
    moreover have "... = setsum (?g ?bb) (?II - J) + (card J)*((?C k)*(f ?B0))" 
    using setsum_constant by (metis real_of_nat_def)
    moreover have "... = (setsum (%i. P(m+onemember2 b0 (?n-(k+1)))) (?II-J)) + 
    (card J)*((?C k)*(f ?B0))" using 6 by force
    moreover have "... = (card (?II - J))*(P(m+ onemember2 b0 (?n-(k+1)))) 
    + (card J)*((?C k)*(f ?B0))"
    using setsum_constant by (metis real_eq_of_nat)
    ultimately have "f ?bb = (card (?II - J))* P (m + onemember2 b0 (?n-(k+1)))
    + (card J)*(?C k)*(f ?B0)" by linarith
    moreover have "card J=k+1" using 12 by force
    moreover have "J \<subseteq> ?II & finite J" using 17 by fast
    then moreover have "card (?II - J)=?n+1 - (k+1)" 
    using 16 12 card_Diff_subset by metis 
    then moreover have 
    29: "?n - k \<noteq> 0" using 12 16 by force
    ultimately have "P (m + onemember2 b0 (?n-(k+1))) = 
    (f ?bb - (k+1)*(?C k)*(f ?B0))/(?n - k)" by force
    moreover have "... = (f ?B0 - (k+1)*(?C k)*(f ?B0))/(?n -k)" using 18 1 by presburger
    ultimately have
    "P (m+onemember2 b0 (?n-(k+1))) = ((f ?B0)*1 -(f ?B0)*((k+1)*(?C k)))/(?n-k)" 
    by force moreover have "... = (f ?B0 * (1 - (k+1)*(?C k)))/(?n-k)" 
    using ll57 by presburger moreover have 
    "... = (f ?B0 * (1 - (k+1)*(?C k)))/(?n-k)" by fastforce 

(* have "?n \<ge> k" by (metis `card (Domain b) + 1 - k \<noteq> 0` diff_is_0_eq nat_le_linear)
then have "real ?n-k=?n -k" by linarith*)

moreover 
have 
    "?C (k+1) = foo (Suc k) (?n)" by auto
    moreover have "... = (%x. (1-((Suc k)*((foo k) x)))/(x-k)) (real ?n)" 
    unfolding foo_def using foo_def by force
    moreover have "... = (1-((Suc k)*((foo k) (?n))))/(?n-k)" using 29 
    by force

ultimately have 
    "P (m+onemember2 b0 (?n-(k+1))) = (f ?B0)*(?C (k+1))" by force 
  }
  thus ?thesis by fastforce
qed

lemma lll54b: fixes X b b0 i1 i2 f P assumes 
"finite b"
"i1 \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
"pred2 b i1 i2 b0 X"
"runiq b"
"\<forall> bb\<in>X. pred0 bb P f"
"pred3 b i1 i2 b0 X f"
shows "\<forall>k::nat. pred1 b b0 i1 i2 f P k \<longrightarrow> pred1 b b0 i1 i2 f P (Suc k)" 
using assms lll54
proof -
let ?p="pred1 b b0 i1 i2 f P"
{
  fix k::nat
  assume "?p k" 
  then have "?p (Suc k)" using assms lll54 by simp
}
thus ?thesis by fast
qed

corollary lll56: fixes X::"(('a \<times> real) set) set" fixes b b0 i1 i2 f P 
assumes 
"finite b"
"(i1::'a) \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
"pred2 b (i1::'a) i2 (b0::real) X"
"runiq b"
"\<forall> bb\<in>X. pred0 bb P f"
"pred3 b i1 i2 b0 X f"
shows "\<forall>n::nat. pred1 b b0 i1 i2 f P n"
proof -
  let ?p="pred1 b b0 i1 i2 f P"
  have 
  1:"finite b" using assms(1) by force
  have
  2: "\<forall> bb\<in>X. pred0 bb P f" using assms(5) by force
  have
  0: "pred2 b (i1::'a) i2 (b0::real) X" using assms(3) by fast
  have 
  3: "i1 \<noteq> i2 & {i1, i2} \<inter> Domain b={}" using assms(2) by linarith
  have "pred1 b b0 i1 i2 f P (0::nat)" using 0 1 2 3 lll55 by fast
  then have
  21: "?p (0::nat)" by fast
  have 
  6: "pred3 b i1 i2 b0 X f" using assms(6) by fast
  have 
  4: "runiq b" using assms(4) by fast
  have 
  22: "\<forall>k::nat. (?p k \<longrightarrow> ?p (Suc k))" using 1 3 0 4 2 6 lll54b by simp
  {
    fix P::"nat => bool" assume 
    23: "P=?p"
    then have "P (0::nat) & (!k::nat. (P k \<longrightarrow> P (Suc k)))" using 21 22 by fastforce
    then have "!n::nat. (P n)" using nat_induct by auto
    then have "\<forall>n::nat. (?p n)" using 23 by fast
  }
  then have "\<forall>P::(nat => bool). P=?p \<longrightarrow> (\<forall>n::nat. ?p n)" by fast
  moreover have "?p=?p" by fast
  ultimately have "!n::nat. ?p n" by presburger
  thus ?thesis by fast
qed

corollary lll57:
assumes
"finite b"
"(i1::'a) \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
"pred2 b (i1::'a) i2 (b0::real) X"
"runiq b"
"\<forall> bb\<in>X. pred0 bb P f"
"pred3 b i1 i2 b0 X f"
shows "P(RRange b + {# b0 #}) = 
(bar (card (Domain b)+1) (card (Domain b)))*f((Domain b \<union> {i1,i2}) \<times> {b0})"
proof -
let ?d=Domain let ?c=card let ?o=onemember2
let ?k="?c (?d b)" let ?m="RRange b" have 
"\<forall>m. ((m\<le>RRange b & size m=?k)\<longrightarrow>P(m + onemember2 b0 (card (Domain b)+1-?k))=
(bar (card (Domain b)+1) ?k)*(f ((Domain b \<union> {i1,i2}) \<times> {b0})))" 
using assms lll56 by fast moreover have "?m \<le> ?m" by fastforce
moreover have "size ?m=?k" using assms by (metis lll30 lll34)
moreover have "?o b0 1={# b0 #}" by (metis ll00 lll52)
ultimately show ?thesis by fastforce
qed

abbreviation const where "const n \<equiv> bar (real (n+1)) n"

abbreviation pred4 where "pred4 F b f P h==(\<forall> i \<in> Domain b. \<exists> j i1 i2 b0 X. 
(F b i=(i1,i2,b0,X) & j \<in> Domain b - {i} & 
pred2 (b outside {i,j}) i1 i2 b0 X & 
pred3 (b outside {i,j}) i1 i2 b0 X f & (b--i)``{j}={b0} & 
(\<forall> bb\<in>X. pred0 bb P f) & 
i1 \<noteq> i2 & ({i1, i2} \<inter> Domain (b outside {i,j}))={} &
f((Domain(b outside {i,j}) \<union> {i1,i2})\<times>{b0})=(h i) b))"

definition counterexample where "counterexample f b1 b2 h=(Domain b1=Domain b2 & 
(* (\<exists> N g. (N\<noteq>0 & h`(Domain b1)={f,g} & {f b2-(f b1), g b2-(g b1)}={0,N}))) *)
(\<exists> g. (h`(Domain b1)={f,g} & {f b2-(f b1), g b2-(g b1)}\<supset>{0})))"

lemma assumes "X \<inter> Y={}" "finite (X \<union> Y)" shows "card (X \<union> Y)=card X + card Y"
using assms by (metis card.union_disjoint finite_Un)

lemma lll05b: assumes "P \<inter> Q={}" "finite (P^-1``{y})" "finite (Q^-1``{y})"
shows "card ((P \<union> Q)^-1``{y}) = card (P^-1``{y}) + card (Q^-1``{y})" 
using assms lll05 lll07 by (metis (hide_lams, no_types) 
Image_iff converse_Int converse_empty emptyE equals0I)

lemma lll05c: assumes "P \<inter> Q={}" "finite (Domain P)" "finite (Domain Q)"
shows "card ((P \<union> Q)^-1``{y}) = card (P^-1``{y}) + card (Q^-1``{y})"
using assms lll05b by (metis (hide_lams, no_types) lll39)

lemma assumes "P \<inter> Q={}" "\<forall>y. finite (P^-1``{y}) & finite (Q^-1``{y})"
shows "(%y. card((P \<union> Q)^-1``{y})) = (%y. (card(P^-1``{y})+card (Q^-1``{y})))"
using assms lll05b by (metis (hide_lams, no_types))

lemma lll05d: assumes "P \<inter> Q={}" "finite (Domain P)" "finite (Domain Q)" shows 
"(%y. card ((P \<union> Q)^-1``{y})) = ((%y. (card (P^-1``{y}) + card (Q^-1``{y}))))"
using assms lll05c by (metis (hide_lams, no_types))

lemma lll58: "(%y. card (P^-1``{y})) + (%y. card (Q^-1``{y}))= 
(%y. (card (P^-1``{y}) + card (Q^-1``{y})))" by fastforce

lemma lll05e: assumes "P \<inter> Q={}" "finite (Domain P)" "finite (Domain Q)" shows 
"(%y. card ((P \<union> Q)^-1``{y})) = (%y. card (P^-1``{y})) + (%y. card (Q^-1``{y}))"
using assms lll05d lll58 
proof -
  have "(%y. card (P^-1``{y})) + (%y. card (Q^-1``{y}))= 
  (%y. (card (P^-1``{y}) + card (Q^-1``{y})))" by fastforce
  moreover have "... = (%y. card ((P \<union> Q)^-1``{y}))" using assms lll05d 
  by (metis (hide_lams, no_types))
  ultimately show ?thesis by presburger
qed

corollary lll05f: assumes "P \<inter> Q={}" 
"finite (Domain P)"
"finite (Domain Q)"
"finite {y. card (P^-1``{y})>0}"
"finite {y. card (Q^-1``{y})>0}"
shows
"RRange (P \<union> Q)=RRange P + RRange Q" using assms lll05e lll10 by metis

corollary lll05g: assumes "P \<inter> Q={}" "finite P" "finite Q" shows
"RRange (P \<union> Q)=RRange P + RRange Q" using assms lll05f lll26 finite_subset 
proof -
  let ?r=Range let ?d=Domain let ?f=finite have 
  "?f (?d P) & ?f (?d Q)" using assms(2,3) by (metis finite_Domain)
  moreover have "?f (?r P) & ?f (?r Q)" using assms(2,3) finite_Range by blast
  ultimately show ?thesis using lll26 lll05f assms finite_subset by metis
qed

lemma lll59: assumes "trivial Y" shows "runiq (X \<times> Y)" using assms 
runiq_def Image_subset ll84 trivial_subset by (metis ll83)

lemma lll66: "RRange ({x} \<times> {y})= {# y #}" using ll00 lll52 lll51 by (metis 
card.insert card_empty comm_monoid_add_class.add.right_neutral empty_iff finite.emptyI)

lemma lll68: fixes F b f P h assumes "pred4 F b f P h"
"finite b"
"runiq b"
shows "(setsum (%i. P(RRange (b--i))) (Domain b))=
(setsum ((%i. (const (card (Domain b)-(2::nat)))*h i b)) (Domain b))"
proof -
let ?R=RRange let ?d=Domain let ?g="%i. P(?R (b--i))" 
let ?C="const (card (?d b)-(2::nat))"
{
  fix i assume 
  4: "i \<in> ?d b" 
  moreover have "pred4 F b f P h" using assms(1) by fast
  ultimately have "\<exists> j i1 i2 b0 X. 
(F b i=(i1,i2,b0,X) & j \<in> Domain b - {i} & 
pred2 (b outside {i,j}) i1 i2 b0 X & 
pred3 (b outside {i,j}) i1 i2 b0 X f & (b--i)``{j}={b0} & (\<forall> bb\<in>X. pred0 bb P f) &
i1 \<noteq> i2 & {i1, i2} \<inter> Domain (b outside {i,j})={} &
f((Domain(b outside {i,j}) \<union> {i1,i2})\<times>{b0})=(h i) b
)" by blast
  then obtain j i1 i2 b0 X where 
  0: "(F b i=(i1,i2,b0,X) & j \<in> Domain b - {i} &
  pred2 (b outside {i,j}) i1 i2 b0 X & 
  pred3 (b outside {i,j}) i1 i2 b0 X f & (b--i)``{j}={b0} & (\<forall> bb\<in>X. pred0 bb P f) &
  i1 \<noteq> i2 & {i1, i2} \<inter> Domain (b outside {i,j})={} &
  f((Domain(b outside {i,j}) \<union> {i1,i2})\<times>{b0})=(h i) b
  )" by metis
  let ?b="b outside {i,j}" let ?bb="(b--i)--j"
  have 
  2: "finite (b--i) & finite ?b" using assms(2) Outside_def by (metis finite_Diff)
  have "b--i = ?bb \<union> (b--i)||{j} " using outside_union_restrict 
  by metis
  moreover have "?b=?bb" by (smt Un_insert_left ll52 sup_bot_left)
  moreover have "(b--i)||{j} \<inter> ?bb={}" by (metis Int_commute lll06b)
  moreover have "finite ?b" using 2 by fast
  ultimately moreover have "finite ((b--i)||{j})" by (metis finite_Un 2)
  ultimately have "?R (b--i) = ?R ?b + ?R ((b--i)||{j})" 
  using lll05g by (metis Int_commute)
  moreover have "?R ((b--i)||{j})=?R({j} \<times> ((b--i)``{j}))" by (metis restrict_to_singleton)
  moreover have "...=?R({j} \<times> {b0})" using 0 by presburger
  moreover have "...={# b0 #}" using lll66 by fast
  ultimately have 
  3: "?R (b--i)=?R ?b + {# b0 #}" by presburger
  have "finite ?b" using 2 by fast
  moreover have "runiq ?b" using assms(3) 
  by (metis lll01 restriction_is_subrel subrel_runiq)
  ultimately
  have "P(?R ?b + {#b0#})=const (card (?d ?b))* f(((?d ?b) \<union> {i1,i2}) \<times> {b0})"
  using 0 lll57 by fast
  moreover have "...=const (card (?d ?b))*(h i) b" using 0 by presburger
  moreover have "?R (b--i)=?R ?b + {# b0 #}" using 3 by fastforce
  ultimately have 
  1: "P (?R (b--i))=
  const (card (?d ?b))*(h i) b" by presburger  
  have "i \<noteq> j" using 0 by blast
  moreover have "i \<in> ?d b" using 4 by auto
  moreover have "j \<in> ?d b" using 0 by force
  moreover have "finite (?d b)" using assms(2) finite_Domain by blast
  ultimately have "card (?d b) - (2::nat) = card (?d b - {i,j})" by auto
  moreover have "...=card (?d ?b)" by (metis outside_reduces_domain)
  ultimately have "const (card (?d ?b))= const (card (?d b) - (2::nat))" by presburger
  then have "P (?R (b--i))= const (card (?d b)-(2::nat))*(h i) b" using 1 by presburger
  then have "?g i = ?C*(h i) b" by fast
}
then have "setsum ?g (?d b) = setsum (%i. ?C* (h i) b) (?d b)"
using setsum_cong2 by fastforce
thus ?thesis by fast
qed

corollary lll63: "const n = 1/(n+2)" using lll67c by auto

lemma lll65: assumes "{x2-x1, y2-y1}={0::real,N}" "0 \<notin> {a,b,N}" shows 
"a*x1 + b*y1 \<noteq> a*x2 + b*y2" (is "?lh \<noteq> ?rh") using assms 
proof -
  have "?rh - ?lh = a*x2 + b*y2 - a*x1 - b*y1" by force
  moreover have "... = a*x2 - a*x1 + b*y2 - b*y1" by force
  moreover have "... = a*x2 - a*x1 + (b*y2 - b*y1)" by auto
  moreover have "... = a*(x2 - x1) + b*(y2 - y1)" using ll57 by fastforce
  moreover have "a \<noteq> 0 & b \<noteq> 0 & N \<noteq> 0" using assms by fast
  then moreover have "(x2-x1=0 & y2-y1 \<noteq> 0) \<or> (x2-x1 \<noteq> 0 & y2-y1 = 0)" using assms(1) by fastforce 
  ultimately moreover have "(a*(x2-x1) = 0 & b*(y2-y1) \<noteq> 0) \<or> (a*(x2-x1) \<noteq> 0 & b*(y2-y1)=0)" 
  by (metis mult_eq_0_iff)
  ultimately have "?rh - ?lh \<noteq> 0" by (metis comm_semiring_1_class.normalizing_semiring_rules(5) comm_semiring_1_class.normalizing_semiring_rules(6))
  thus ?thesis by force
qed

lemma lll70: (*unused*) "{a} \<subset> {x,y} = (\<exists>b. b \<noteq> a & {x,y}={a,b})" using assms by blast

lemma lll65b: assumes "{0} \<subset> {x2-x1, y2-y1}" "\<not> {0} \<subseteq> {a::real, b}"
shows "a*x1 + b*y1 \<noteq> a*x2 + b*y2" using lll65 assms by auto
(* lll65 with equivalent hypotheses *)

lemma lll69: assumes "counterexample f b1 b2 h" 
"card (Domain b1) \<ge> 2" (* implies finiteness *)
shows 
" setsum((%i. (const(card(Domain b1)-(2::nat)))*(h i b1))) (Domain b1) - (f b1)
\<noteq> setsum((%i. (const(card(Domain b2)-(2::nat)))*(h i b2))) (Domain b2) - (f b2)"
proof -
  let ?d=Domain
  let ?I1="?d b1" let ?I2="?d b2" let ?n="(card ?I1) - (2::nat)" 
  let ?C="const ?n"
  have 
  3: "finite ?I1" using assms(2) card_def by (metis not_numeral_le_zero)
  have 
  4: "?I1=?I2" using assms counterexample_def by metis    
  have "?n+(2::nat)=card ?I1" using assms(2) by fastforce
  then have 
  1: "card ?I1 \<ge> 2 & ?C=1/(card ?I1)" using lll63 by force
  let ?f1="%i. ?C * (h i b1)" 
  let ?f2="%i. (const ((card ?I1) - (2::nat))) * (h i b2)"
  let ?F="?I1 \<inter> h-`{f}"   
  (* obtain N g where 
  0: "N \<noteq> 0 & h`(Domain b1)={f,g} & {f b2-(f b1), g b2 - (g b1)}={0,N}" 
  using assms counterexample_def sorry *)
  obtain g where 
  0: "h`(Domain b1)={f,g} & {f b2-(f b1), g b2 - (g b1)} \<supset> {0}" 
  using assms counterexample_def by metis
  let ?G="h-`{g} \<inter> ?I1" 
  have "{f} \<subseteq> h` ?I1 & {g} \<subseteq> h` ?I1 " using 0 by blast
  then have "?F \<noteq> {} & ?G \<noteq> {}" using vimage_def by force
  then have 
  2: "?F \<noteq> {} & ?G \<noteq> {} & ?G \<subseteq> ?I1 & ?F=?I1 - ?G" using 0 by auto   
  have 
  "setsum ?f1 ?I1 = setsum ?f1 (?I1 - ?G) + (setsum ?f1 ?G)" 
  using 0 2 3 setsum_subset_diff by smt
  then have "setsum ?f1 ?I1 = setsum ?f1 ?F + setsum ?f1 ?G" using 2 by presburger
  moreover have "... = setsum (%i. ?C* (f b1)) ?F + setsum (%i. ?C* (g b1)) ?G"
  by auto
  moreover have "... = of_nat (card ?F) * (?C*(f b1)) + of_nat (card ?G) * (?C*(g b1))"
  using setsum_constant by force
  moreover have "... = card ?F * (?C*(f b1)) + (card ?G * (?C*(g b1)))" 
  using real_eq_of_nat by presburger
  ultimately have "setsum ?f1 ?I1 = card ?F * (?C*(f b1)) + card ?G * (?C*(g b1))" 
  by presburger
  then have "setsum ?f1 ?I1 = card ?F * ?C * (f b1)+ card ?G * ?C * (g b1)" 
  by linarith
  then have "setsum ?f1 ?I1 - (f b1) = 
  (card ?F * ?C)*(f b1) - (1::nat)*(f b1) + ((card ?G)*?C*(g b1))" by linarith
  moreover have "...=(card ?F * ?C-(1::nat))*(f b1)+((card ?G)*?C*(g b1))" 
  using lll62 by presburger
  ultimately have 
  11: "setsum ?f1 ?I1 - (f b1) = (card ?F * ?C-(1::nat))*(f b1)+((card ?G)*?C*(g b1))"
  by presburger
  have "setsum ?f2 ?I2 = setsum ?f2 (?I1 - ?G) + (setsum ?f2 ?G)" 
  using 0 2 3 4 setsum_subset_diff by smt  
  then have "setsum ?f2 ?I2 = setsum ?f2 ?F + setsum ?f2 ?G" using 2 by presburger
  moreover have "... = setsum (%i. ?C* (f b2)) ?F + setsum (%i. ?C* (g b2)) ?G"
  by auto
  moreover have "... = of_nat (card ?F) * (?C*(f b2)) + of_nat (card ?G) * (?C*(g b2))"
  using setsum_constant by force
  moreover have "... = card ?F * (?C*(f b2)) + (card ?G * (?C*(g b2)))" 
  using real_eq_of_nat by presburger
  ultimately have "setsum ?f2 ?I2 = card ?F * (?C*(f b2)) + card ?G * (?C*(g b2))" 
  by presburger
  then have "setsum ?f2 ?I2 = card ?F * ?C * (f b2)+ card ?G * ?C * (g b2)" 
  by linarith
  then have "setsum ?f2 ?I2 - (f b2) = 
  (card ?F * ?C)*(f b2) - (1::nat)*(f b2) + ((card ?G)*?C*(g b2))" by linarith
  moreover have "...=(card ?F * ?C-(1::nat))*(f b2)+((card ?G)*?C*(g b2))" 
  using lll62 by presburger
  ultimately have 
  12: "setsum ?f2 ?I2 - (f b2) = (card ?F * ?C-(1::nat))*(f b2)+((card ?G)*?C*(g b2))"
  by presburger  
  have "?F < ?I1" using 2 by fastforce
  then have "card ?F < card ?I1" 
  using 3 psubset_card_mono by metis
  moreover have "card ?G \<noteq> 0" using 3 2 by simp
  ultimately have "card ?F * ?C - (1::nat) \<noteq> 0 & card ?G *?C \<noteq> 0" using 1 by simp
  (* hen have "0 \<notin> {card ?F * ?C - (1::nat), card ?G * ?C, N}" using 0 by auto
  moreover have "{(f b2)-(f b1), (g b2) - (g b1)} = {0,N}" using 0 by fast *)
  then have "(card ?F * ?C-(1::nat))*(f b1)+((card ?G)*?C*(g b1)) \<noteq> 
  (card ?F * ?C-(1::nat))*(f b2)+((card ?G)*?C*(g b2))"
  using lll65b 0 by auto
  then have "setsum ?f1 ?I1 - (f b1) \<noteq> 
  (card ?F * ?C-(1::nat))*(f b2)+((card ?G)*?C*(g b2))" using 11 by presburger   
  then have "setsum ?f1 ?I1 - (f b1) \<noteq> setsum ?f2 ?I2 - (f b2)" using 12 by presburger
  thus ?thesis using 4 by auto
qed

corollary assumes
"finite b1"
"finite b2"
"runiq b1"
"runiq b2"
"pred4 F1 b1 f1 P h"
"pred4 F2 b2 f2 P h"
"counterexample f b1 b2 h"
"card (Domain b1) \<ge> 2"
shows
"setsum (%i. P(RRange (b1--i))) (Domain b1) - (f b1) 
\<noteq> 
 setsum (%i. P(RRange (b2--i))) (Domain b2) - (f b2)"
using assms lll68 lll69
proof -
have "setsum (%i. P(RRange (b1--i))) (Domain b1) = 
setsum ((%i. (const (card (Domain b1)-(2::nat)))*h i b1)) (Domain b1)"
using assms(1,3,5) lll68 by fast
then have "setsum (%i. P(RRange (b1--i))) (Domain b1) - f b1 = 
setsum ((%i. (const (card (Domain b1)-(2::nat)))*h i b1)) (Domain b1) - f b1"
by presburger
moreover have "setsum (%i. P(RRange (b2--i))) (Domain b2) = 
setsum ((%i. (const (card (Domain b2)-(2::nat)))*h i b2)) (Domain b2)" 
using assms(2,4,6) lll68 by fast
then moreover have "setsum (%i. P(RRange (b2--i))) (Domain b2) - f b2 = 
setsum ((%i. (const (card (Domain b2)-(2::nat)))*h i b2)) (Domain b2) - f b2"
by presburger
moreover have "
setsum ((%i. (const (card (Domain b1)-(2::nat)))*(h i b1))) (Domain b1) - (f b1)
\<noteq> 
setsum ((%i. (const (card (Domain b2)-(2::nat)))*(h i b2))) (Domain b2) - (f b2)"
using assms(7,8) lll69 by blast
ultimately show ?thesis by presburger
qed

corollary lll60: fixes X b i1 I1 I2 P f fixes b0::real
assumes "I1 \<noteq> I2" "finite b" "runiq b" "i1 \<in> {I1,I2} \<union> Domain b"
"{I1,I2} \<inter> Domain b={}" "\<forall> bb\<in>X. pred0 bb P f"
"pred22 (b +< ({I1,I2} \<times> {b0})) I1 I2 b0 X"
"pred33 (b +< ({I1,I2} \<times> {b0})) I1 I2 b0 X f"
shows "P (RRange ( (b +< ({I1,I2} \<times> {b0})) -- i1))=
(bar (card (Domain b)+1) (card (Domain b)))*f((Domain b \<union> {I1,I2}) \<times> {b0})"
proof -
  let ?d=Domain let ?c=card let ?R=RRange let ?u=runiq let ?t=trivial
  let ?B="b +< ({I1,I2} \<times> {b0})" let ?BB="b \<union> ({I1,I2} \<times> {b0})" let ?n="?c (?d b)"
  have 
  22: "?d b \<inter> {I1,I2}={}" using assms(5) by blast
  moreover have "?d ({I1,I2}\<times>{b0})={I1,I2}" by simp
  ultimately have 
  23: "?BB=?B" using paste_disj_domains by metis  
  have 
  1: "I1 \<noteq> I2" using assms(1) by fast then obtain i2 where 
  0: "i2 \<in> {I1,I2}-{i1}" by blast
  let ?b="(?B -- i2) -- i1" let ?I="{I1,I2}-{i2}" have
  20: "?b=?B outside {i1,i2}" using ll52 by (metis doubleton_eq_iff insert_is_Un)
  have "?u ({I1,I2}\<times>{b0})" using lll59 by (metis trivial_singleton)
  then have "?u ?B" using assms by (metis runiq_paste2)
  then have "?u (?B--i2) & ?u (?B--i1)" using Outside_def by (metis Diff_subset subrel_runiq)
  then have 
  14: "?u ?b" using Outside_def by (metis Diff_subset subrel_runiq)  
  have "finite ({I1,I2}\<times>{b0})" by fast
  moreover have "?B \<subseteq> b \<union> ({I1,I2}\<times>{b0})" by (metis paste_sub_Un)
  ultimately have 
  21: "finite ?B" using assms(2) paste_def finite_subset by fast
  then have
  "finite (?B -- i2)" using Outside_def by (metis finite_Diff)
  then have 
  11: "finite ?b" using Outside_def by (metis finite_Diff) 
  have "i1 \<noteq> i2" using 0 by fastforce
  moreover have "?d ?b \<inter> {i1,i2}={}" using 20 Outside_def by (smt Diff_disjoint inf.commute outside_reduces_domain)
  ultimately have
  12: "i1 \<noteq> i2 & ?d ?b \<inter> {i1, i2}={}" by fastforce
  have
  15: "\<forall> bb\<in>X. pred0 bb P f" using assms by fast  
  have "?d ?b=?d ?BB-{i1,i2}" using Outside_def 20 23 by auto
  moreover have "i1 \<in> ?d ?BB" using assms(4) by force
  moreover have "i2 \<in> ?d ?BB" using 0 22 by fast
  ultimately have "?d ?b \<union> {i1,i2} = ?d ?BB" by auto
  moreover have "...=?d b \<union> {I1,I2}" by auto
  ultimately moreover have 
  24: "?d ?b \<union> {i1,i2}=?d b \<union> {I1,I2} & ?d ?BB=?d b \<union> {I1,I2}" by presburger
  moreover have "finite (?d b) & finite {I1,I2}" using assms finite_Domain by blast
  moreover have "finite (?d ?b) & finite {i1,i2}" using 11 finite_Domain by fast
  ultimately moreover have "?n + ?c {I1,I2}=?c (?d ?BB)" using 22 by (smt card.union_disjoint)
  ultimately moreover have "...=?c (?d ?b)+ ?c{i1,i2}" using 12 by (smt card.union_disjoint)
  ultimately have "?n + 2=?c (?d ?b)+2" using 0 1 by auto
  then have 
  31: "?n=?c (?d ?b)" by auto  
  have "(?B--i1) = ((?B -- i1) -- i2) \<union> ({i2} \<times> ((?B -- i1)``{i2}))"
  using Outside_def by blast
  moreover have "... = (?B outside {i1,i2}) \<union> ({i2} \<times> ((?B--i1)``{i2}))"
  using ll52 by (metis insert_is_Un)
  moreover have "... = ?b \<union> ({i2} \<times> ((?B--i1)``{i2}))" using 20 by presburger
  moreover have "... = ({i2} \<times> ((?B--i1)``{i2})) \<union> ?b" by fastforce
  ultimately moreover have "?R(?B--i1)=?R(({i2} \<times> ((?B--i1)``{i2})) \<union> ?b)" by presburger
  moreover have "?d ({i2} \<times> ((?B--i1)``{i2})) \<subseteq> {i2}" by fast
  moreover have "?d ?b=?d ?B - {i1,i2}" using 20 by (metis outside_reduces_domain)
  ultimately moreover have "{i2} \<times> ((?B--i1)``{i2}) \<inter> ?b={}" using 20 Outside_def 
  by auto
  ultimately moreover have "finite ({i2} \<times> ((?B--i1)``{i2}))" 
  using 21 Outside_def by (metis finite_Diff finite_Un)
  ultimately moreover have "RRange (({i2} \<times> ((?B--i1)``{i2})) \<union> ?b) = 
  RRange ({i2} \<times> ((?B--i1)``{i2})) + RRange ?b" using lll05g 11 by metis
  ultimately have "?R (?B--i1) = ?R ({i2}\<times>((?B--i1)``{i2})) + ?R ?b" by presburger
  moreover have "(?B--i1)``{i2}=?B``({i2}-{i1})" using Outside_def Image_def by auto
  moreover have "...=?BB``{i2}" using 0 23 by blast
  moreover have "...=b``{i2} \<union> ({I1,I2}\<times>{b0})``{i2}" by fast
  moreover have "...={} \<union> ({I1,I2}\<times>{b0})``{i2}" using 22 0 by fast
  moreover have "...={b0}" using 0 by fast
  ultimately have "?R (?B--i1)=?R({i2}\<times>{b0}) + ?R ?b" by presburger
  moreover have "?R({i2}\<times>{b0})= onemember b0 1" 
  using lll51 
  (* by (metis Nat.add_0_right card.insert card_empty empty_iff finite.emptyI lll44 lll45 lll46)*)
  by (metis card.insert card_empty empty_iff finite.emptyI lll52 monoid_add_class.add.right_neutral)
  moreover have "...={#b0#}" by (metis ll00) 
  ultimately have "{#b0#}+?R ?b  = ?R (?B -- i1)" by presburger
  then have
  32: "?R ?b + {#b0#}= ?R (?B -- i1)" using add_commute by metis
  have "pred22 ?B I1 I2 b0 X" using assms by fastforce (*?B or b ?*)
  moreover have "pred33 ?B I1 I2 b0 X f" using assms by fast (*?B or b ?*)
  moreover have "i1 \<in> {I1,I2} \<union> (?d ?B)" using 0 23 24 assms 
  by (smt Un_commute Un_empty_left Un_insert_left insert_absorb2)
  then moreover have "i1 \<in> {I1,I2} \<union> (?d ?B)-{i2}" using 0 by force
  moreover have "i2\<in>{I1,I2}" using 0 by fast
  ultimately moreover have 
  13: "pred2 ?b i1 i2 b0 X" using pred22_def 20 by metis
  ultimately have 
  16: "pred3 ?b i1 i2 b0 X f" using pred33_def 20 by metis  
  have "P(?R ?b + {# b0 #})=bar (?c (?d ?b)+1) (?c (?d ?b))*
  f (((?d ?b) \<union> {i1, i2}) \<times> {b0})" using 11 12 13 14 15 16 lll57 by fast
  then have 
  "P (?R(?B--i1))=bar (?n+1) ?n* f((?d b \<union> {I1,I2}) \<times> {b0})" 
  using 24 31 32 by metis
  thus ?thesis by linarith
qed

corollary 
fixes X b i1 I1 I2 P f fixes b0::real
assumes "I1 \<noteq> I2" "finite b" "runiq b" 
"{I1,I2} \<inter> Domain b={}" "\<forall> bb\<in>X. pred0 bb P f"
"pred22 (b +< ({I1,I2} \<times> {b0})) I1 I2 b0 X"
"pred33 (b +< ({I1,I2} \<times> {b0})) I1 I2 b0 X f"
"pred0 (b +< ({I1,I2}\<times>{b0})) P f"
shows "setsum (%i. P (RRange ((b+< ({I1,I2}\<times>{b0})) -- i))) ({I1,I2} \<union> Domain b) = 
(bar (card (Domain b)+1) (card (Domain b)))*f((Domain b \<union> {I1,I2}) \<times> {b0})*
(card(Domain b)+2)"
proof -
let ?d=Domain let ?c=card
let ?B="b +< ({I1,I2}\<times>{b0})" let ?f="%i. P (RRange (?B--i))" let ?n="?c (?d b)"
let ?I="?d b" let ?i="{I1,I2}"
{
  fix i1 assume 
  0: "i1 \<in> {I1,I2} \<union> Domain b"
  have "P(RRange (?B--i1))=(bar (?n+1) ?n)*f((?I \<union> ?i) \<times>{b0})" 
  using assms(1) assms(2) assms(3) 0 assms(4) assms(5) assms(6) assms(7) lll60
  by simp
  then have "?f i1=(bar (?n+1) ?n)*f((?I \<union> ?i) \<times>{b0})" by fastforce
}
then have "setsum ?f (?i \<union> ?I)=setsum (%i. (bar (?n+1) ?n)*f((?I \<union> ?i)\<times>{b0}))
(?i \<union> ?I)" using setsum_cong2 by force
moreover have "...=of_nat(?c (?i \<union> ?I)) * ((bar (?n+1) ?n)*f((?I \<union> ?i)\<times>{b0}))"
using setsum_constant by blast
ultimately have "setsum ?f (?i \<union> ?I)= (?c (?i \<union> ?I))*bar (?n+1) ?n * 
f((?i \<union> ?I) \<times> {b0})" using real_eq_of_nat by force
moreover have "finite ?i & finite ?I" using assms finite_Domain by fast
then moreover have "?c (?i \<union> ?I) = ?n + ?c ?i" 
using card.union_disjoint assms(1,2,4) by force
moreover have "... = ?n+2" using assms(1) by force
ultimately show ?thesis by auto
have "setsum ?f (?d ?B)=f ?B" using assms (8) by force
moreover have "?d (?i\<times>{b0})=?i" by force
then moreover have "?d ?B=?i \<union> ?I" using assms by (smt paste_Domain sup_commute)
ultimately have "setsum ?f (?i \<union> ?I)=f ?B" by force
have "(?n+2)*bar (?n+1) ?n * f((?i \<union> ?I)\<times>{b0}) = f ?B" sorry
moreover have "... = f((?i \<union> ?I) \<times> {b0})" sorry
ultimately have "(?n+2)*bar (?n+1) ?n * f((?i \<union> ?I)\<times>{b0}) = f((?i \<union> ?I)\<times>{b0})"
sorry
qed

(*
lemma shows "inj_on ler_in UNIV" using assms inj_on_def sorry
lemma fixes n shows "count (Abs_multiset id) n = 1" sorry
lemma "onemember x n = onemember2 x n" using assms onemember_def sorry
lemma shows "onemember (1::nat) 2 = {# 1, 1 #}" using onemember_def single_def 
ll00 sorry

definition pred where "pred f C \<eta> P M x n = 
(\<forall> m. RRange m \<subseteq># M & size (RRange m)=n \<longrightarrow> 
(P (onemember x (1+size M - n) + (RRange m)) = (C \<eta> n) * (f m)))"

definition foo where "foo x M n = 
{{# x, x #} + (onemember x (size M - n)) + m|m. m \<subseteq># M & size m=n}"
lemma shows "inj (foo x M)" sorry
definition bar where "bar x M = (\<Union> n\<in>{0::nat ..< (1+size M)}. foo x M n)"
definition closed where "closed X x M = ((RRange ` X) \<supseteq> bar x M)"
definition dotprod where "dotprod (f::'a => real) g X = (setsum (f*g) X)" 

lemma fixes f::"'a => nat" fixes g::"'a => nat" shows 
"(Abs_multiset (%x. ((f x) + (g x)))) = 
((Abs_multiset f) + (Abs_multiset g))"
using plus_multiset_def multiset_eq_iff assms sorry

*)

end
