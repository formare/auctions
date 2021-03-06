theory Maskin3

imports 
(* Scraps2 *)
RelationQuotient
(* "~~/src/HOL/Cardinals/Cardinal_Order_Relation_Base" *) 
(* SupInf *)
"../Vcg/RelationProperties"
Real_Vector_Spaces
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

term size














section {*Preliminaries*}

value "{# 1::nat #} + {# 1::nat #}"

lemma lll61: fixes x::real fixes y z 
shows "x/z-(y/z)=(x-y)/z" 
using assms by (metis diff_divide_distrib)

lemma lll64: fixes x::int shows "x-y+y=x" by force

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
using assms converse_Un Un_Image by (metis Nat.add_0_right card_Un_Int card_empty)

lemma lll08: fixes f assumes "finite {x. f x>0}" shows
"count (Abs_multiset f) = f" using assms 
by (metis (full_types) Abs_multiset_inverse mem_Collect_eq multiset_def)

lemma lll09: shows "Abs_multiset o count=id" using count_inverse by fastforce

lemma ll57: (*repetition*) fixes a::real fixes b c shows "a*b - a*c=a*(b-c)"
using assms by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

lemma lll62: fixes a::real fixes b c shows "a*b - c*b=(a-c)*b"
using assms ll57 by (metis comm_semiring_1_class.normalizing_semiring_rules(7))

lemma ll44: fixes x::real fixes y z shows "x*(y + z)=x*y + x*z" 
by (metis comm_semiring_1_class.normalizing_semiring_rules(34))

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
using assms  setsum.reindex by (metis(no_types) id_comp)
lemma lll27: "{y. (P^-1``{y}) \<noteq> {}} \<supseteq> Range P" using assms by fast
lemma lll28: assumes "\<forall>y. finite (P^-1``{y})" 
shows "{y. (P^-1``{y}) \<noteq> {}} = {y. card (P^-1``{y})>0}" using assms by auto
lemma lll29: assumes "\<forall>y. finite (P^-1``{y})" shows 
"{y. card (P^-1``{y}) > 0} = Range P" using assms lll26 lll27 lll28 
by (metis subset_antisym)

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
then moreover have "setsum card ?B = setsum (card o ?f) (?r P)" using setsum.reindex_cong
by fastforce
ultimately moreover have "setsum (card o ?f) (?r P) = setsum (card o ?g) (?r P)" 
using setsum.cong by fast
ultimately have "setsum card ?B = setsum (card o ?g) (?r P)" by presburger
moreover have "finite {yy. (%y. card (P^-1``{y})) yy > 0}" using 1
by (metis (full_types) finite_Range lll26 rev_finite_subset)
then moreover have "count (RRange P) = (%y. card (P^-1``{y}))" using lll08 lll09 by fast
moreover have "... = card o ?g" by fastforce
ultimately moreover have "size (RRange P)=
setsum (card o ?g) (set_of (RRange P))" using size_multiset_overloaded_eq by (metis)
ultimately moreover have "set_of (RRange P) = {y. (card o ?g) y>0}" 
using set_of_def by metis 
ultimately moreover have "... = Range P" using lll29 2 by metis
ultimately moreover have "size (RRange P) = setsum (card o ?g) (?r P)" using lll29 
by presburger
ultimately have "size (RRange P)=setsum card ?B" by presburger
moreover have "P = \<Union> ?B" by auto
moreover have "finite P" using 1 by fast
ultimately moreover have "finite ?B" using 1 finite_UnionD by (metis(no_types,lifting))
ultimately moreover have "\<forall>A\<in>?B. finite A" by blast
ultimately moreover have "(ALL A:?B. ALL B:?B. A \<noteq> B --> A Int B = {})"
by blast
ultimately moreover have "card (Union ?B) = setsum card ?B" using card_Union_disjoint
by fast
ultimately moreover have "... = size (RRange P)" by presburger
ultimately moreover have "size (RRange P)=card (\<Union> ?B)" by presburger
ultimately show "size (RRange P)=card P" by presburger
qed

lemma lll12: "P``X \<subseteq> (P \<union> Q)``X" using assms by fast

lemma lll13: fixes P Q x assumes "P \<subseteq> Q" "finite (Q``{x})" shows 
"card (P``{x}) \<le> card (Q``{x})"
using assms card_mono lll12 by (metis subset_Un_eq)

lemma lll14: assumes "P \<subseteq> Q" "\<forall>y. finite (Q^-1``{y})" 
(* "finite {y. card (Q^-1``{y}) > 0}" *)
shows
"!y. (%y. (card (P^-1``{y}))) y \<le> (%y. (card (Q^-1``{y}))) y" 
using assms lll13 by (metis converse_mono)

lemma lll35: fixes P Q y assumes "P \<subseteq> Q" 
"finite (Q^-1``{y})"
shows "card (P^-1 `` {y}) \<le> card (Q^-1``{y})"
using assms by (metis converse_mono lll13)

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

lift_definition onemember :: "'a => nat => 'a multiset" is 
"\<lambda>a n b. if b = a then n else 0" by (metis only1_in_multiset)

abbreviation onemember2 
::"'a => nat => 'a multiset"
where "onemember2 x n == RRange ({1..<n+1}\<times>{x})"

abbreviation "singlenton x n == onemember2 x n"

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

lemma assumes "X \<inter> Y={}" "finite (X \<union> Y)" shows "card (X \<union> Y)=card X + card Y"
using assms finite_Un by (metis card_Un_disjoint)

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

lemma lll66: "RRange ({x} \<times> {y})= {# y #}" using ll00 lll52 lll51 
card.insert card_empty empty_iff finite.emptyI by (metis One_nat_def)

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























section {*Foobarconst*}

fun foo ::"nat => (real (* could be real *) => real)" where 
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

corollary lll67b: fixes x::real shows
"\<forall>k. (k<x \<longrightarrow> foo k x=1/(x+1)) \<longrightarrow> ((Suc k < x) \<longrightarrow> foo (Suc k) x=1/(x+1))" 
using lll67 by simp

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
corollary lll67d: fixes x::real fixes k::nat shows
"\<forall>k. k<x \<longrightarrow> bar x k =1/(x+1)" using lll67c by auto
abbreviation const where "const n \<equiv> bar (real (n+1)) n"
corollary lll63: "const n = 1/(n+2)" using lll67c by auto























































section {*Maskin's 3*}

abbreviation pred0 where "pred0 b P f == (setsum (%i. P (RRange (b -- i))) (Domain b) = f b)"

lemma lll53: 
(* fixes b::"('a \<times> real) set" fixes P::"real multiset => real"
fixes b0::real fixes i1::'a fixes i2::'a
fixes m::"real multiset" fixes f::"('a \<times> real) set => real" *)
assumes 
"finite (Domain b)"
"i1 \<noteq> i2 & Domain b \<inter>{i1,i2}={}"
"pred0 ((Domain b \<union> {i1,i2}) \<times> {b0}) P f"
"size m=0"
shows "
(* \<forall>m. ((m \<le> RRange b & (size m)=(0::nat)) \<longrightarrow> *)
(P(m + (onemember2 b0 (card (Domain b)+1 - (0::nat))))=
(bar (card (Domain b)+1) (0))*(f ((Domain b \<union> {i1,i2}) \<times> {b0})))" 
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
  using setsum.cong by force
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

abbreviation pred1 where (* Proof by induction on k *)
"pred1 b b0 (i1::'a) (i2::'a) f P (k::nat) == 
\<forall>m. (m \<le> RRange b & size m=k)\<longrightarrow> (P(m + onemember2 b0 (card (Domain b)+1-k))=
(bar (card (Domain b)+1) k)*f ((Domain b \<union> {i1,i2})\<times>{b0}))"

definition pred2 where "pred2 b i1 i2 b0 X =
(\<forall> m. ((m\<le>RRange b) \<longrightarrow> (\<exists> J. 
(J \<subseteq> Domain b & ((Domain b \<union> {i1,i2})\<times>{b0}) +< (b||J) \<in> X & RRange(b||J)=m))))"

definition pred3 where "pred3 b i1 i2 b0 X f = 
(\<forall> J. (((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b || J) \<in> X) \<longrightarrow> 
(f (((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b||J)) = f ((Domain b \<union> {i1,i2}) \<times> {b0})))"

lemma lll55: (* fixes X::"(('a \<times> real) set) set" fixes b b0 i1 i2 f P *)
assumes
(* "\<forall> (m::real multiset). (m \<le> RRange b) \<longrightarrow> (\<exists> (J::'a set) \<subseteq> Domain b. 
((Domain b \<union> {i1,i2}) \<times> {b0}) +< (b || J) \<in> X & RRange (b || J) = m)" *)
"pred2 b i1 i2 b0 X"
"finite b"
"\<forall> bb\<in>X. pred0 bb P f"
"i1 \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
shows "pred1 b b0 i1 i2 f P (0::nat)"
proof -   
  let ?d=Domain let ?I12="{i1, i2}" let ?I="?d b" let ?M="RRange b" 
  let ?II="?I \<union> ?I12" let ?n="card ?I+1" let ?B0="?II\<times>{b0}" let ?C="bar ?n"
  have
  11: "\<forall> (m). (m \<le> RRange b) \<longrightarrow> (\<exists> (J::'a set) \<subseteq> Domain b. 
  ((Domain b \<union> {i1,i2}) \<times> {b0}) +* (b || J) \<in> X & RRange (b || J) = m)" using
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
  ultimately show ?thesis using lll53 by fastforce
qed

lemma lll54: (* fixes X b fixes b0::real fixes i1::'a fixes i2 f P fixes k::nat  *)
assumes 
"finite b"
"i1 \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
"pred2 b i1 i2 b0 X"
"runiq b"
"pred1 b b0 i1 i2 f P k"
"\<forall> bb\<in>X. pred0 bb P f"
"pred3 b i1 i2 (b0::real) X f"
shows "pred1 b b0 i1 i2 f P (Suc k)" 
proof -
  let ?R1="% P y. (P^-1``{y})" let ?R="%P y. card (?R1 P y)" let ?u=runiq
  let ?d=Domain let ?I12="{i1, i2}"
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
    using 1 16 by auto have 
    17: "finite J & J \<subseteq> ?II" using 1 16 rev_finite_subset by auto
    then have 
    11: "finite (Domain (b||J))" by (metis finite_Int ll41)
    have "?bb=?B0 outside (?d (b || J)) \<union> (b || J)" by (metis paste_def)
    moreover have "... = ?B0 outside J \<union> (b || J)" using 1 Int_absorb1 ll41 by (metis(lifting))
    ultimately have 
    9: "?bb = (?B0 outside J) \<union> (b || J)" by presburger
    let ?h="%i. P(m+onemember2 b0 (?n-(k+1)))"

    have 
    6: "\<forall>i. ((i \<in> (?II - J)) \<longrightarrow> (((?g ?bb) i) = (?h i)))"
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
        ultimately moreover have "finite ((?B0 outside (J \<union> {i}))^-1``{y})" 
        using rev_finite_subset by (metis(no_types))
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
        also have "... = P(m+(RRange (?B0 outside (J \<union> {i}))))" by (metis union_commute)
        also have "... = P(m+(onemember2 b0 (?n + 1 - (k+2))))" using 19 by presburger
        ultimately show "(?g ?bb) i=(?h i)" by force  
      qed
    qed 
  
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
        using 13 inf_sup_aci(5) insert_absorb insert_is_Un by force
        moreover have "?d (?B0 outside J) \<inter> J={}" 
        using outside_reduces_domain by fast
        moreover have "?d (b||(J-{i})) \<subseteq> J-{i}" using ll41 Int_lower2 by (metis)
        ultimately moreover have 
        "\<forall>y. (?B0 outside J)^-1``{y} \<inter> ((b || (J-{i}))^-1``{y})={}" by blast
        moreover have "\<forall>y. finite ((?B0 outside J)^-1``{y})" 
        using lll39 finite_Domain 25 by fast
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
          using 12 13 17 add_diff_cancel_left' card_Diff_singleton_if by (metis add.commute)
          ultimately
          have "size (RRange (b||(J-{i}))) = k" using 7 1 13 by presburger (*MC: here I need runiq b*)
          moreover have "RRange (b||(J-{i})) \<le> ?M" using 7 1 8 by force
          ultimately have "P(RRange (b||(J-{i})) + onemember2 b0 (?n-k))=
          (?C k)*(f ?B0)" using 4 by blast
          moreover have "RRange (?B0 outside J)=onemember2 b0 (?n-k)" 
          using 23 by fastforce
          ultimately have 
          "(?C k)*(f ?B0) = P(RRange (?B0 outside J) + (RRange (b||(J-{i}))))" 
          using add.commute by (metis(no_types))
          also have "... = (?g ?bb) i" using 14 by presburger
          finally have "(%i. (?C k)*(f ?B0)) i = (?g ?bb) i" by fastforce
          thus ?thesis by presburger
        qed
      }
      thus ?thesis by fastforce
    qed (* 5 *)

    have "?d ?B0 = ?II" by auto then
    have "?d ?bb = ?II" using 1 
    Int_absorb1 Un_insert_right insert_is_Un ll41 ll54 paste_Domain sup.commute by (metis(lifting,no_types))
    then have "f ?bb = setsum (?g ?bb) ?II" using 1 2 by fastforce
    moreover have "... = setsum (?g ?bb) (?II - J) + setsum (?g ?bb) J" 
    using setsum.subset_diff 1 17 16 by auto
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

lemma lll54b: (* fixes X b b0 i1 i2 f P *)
assumes 
"finite b"
"i1 \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
"pred2 b i1 i2 b0 X"
"runiq b"
"\<forall> bb\<in>X. pred0 bb P f"
"pred3 b i1 i2 (b0::real) X f"
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

lemma lll56: (* fixes X::"(('a \<times> real) set) set" fixes b b0 i1 i2 f P  *)
assumes 
"finite b"
"(i1::'a) \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
"pred2 b (i1::'a) i2 b0 X"
"runiq b"
"\<forall> bb\<in>X. pred0 bb P f"
"pred3 b i1 i2 (b0::real) X f"
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
  then have "!n::nat. ?p n" by presburger
  thus ?thesis by fast
qed

corollary lll57:
assumes
"finite b"
"(i1::'a) \<noteq> i2 & {i1, i2} \<inter> Domain b={}"
"pred2 b (i1::'a) i2 (b0) X"
"runiq b"
"\<forall> bb\<in>X. pred0 bb P f"
"pred3 b i1 i2 (b0::real) X f"
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

lemma lll68: (* fixes F b f P h *)
assumes "pred4 F (b::(_ \<times> real) set) f P h"
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
  moreover have "?b=?bb" using Un_insert_left ll52 sup_bot_left by metis
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
  moreover have "?R (b--i)=?R ?b + {# b0 #}" using 3 by fastforce ultimately have 
  1: "P (?R (b--i))=const (card (?d ?b))*(h i) b" by presburger  
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
then have "setsum ?g (?d b) = setsum (%i. ?C* (h i) b) (?d b)" using setsum.cong by fastforce
thus ?thesis by fast
qed

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
  3: "finite ?I1" using assms(2) card_def not_numeral_le_zero by fastforce
  have 
  4: "?I1=?I2" using assms counterexample_def by metis    
  have "?n+(2::nat)=card ?I1" using assms(2) by fastforce
  then have 
  1: "card ?I1 \<ge> 2 & ?C=1/(card ?I1)" using lll63 by force
  let ?f1="%i. ?C * (h i b1)" 
  let ?f2="%i. (const ((card ?I1) - (2::nat))) * (h i b2)"
  let ?F="?I1 \<inter> h-`{f}"
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
  using 0 2 3 setsum.subset_diff by (metis(no_types))
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
  using 0 2 3 4 setsum.subset_diff by (metis(no_types))
  then have "setsum ?f2 ?I2 = setsum ?f2 ?F + setsum ?f2 ?G" using 2 by presburger
  moreover have "... = setsum (%i. ?C* (f b2)) ?F + setsum (%i. ?C* (g b2)) ?G" by auto
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

corollary tt01: assumes
"finite b1"
"finite b2"
"runiq b1"
"runiq b2"
"pred4 F1 (b1::(_ \<times> real) set) f1 (P::_ => real) h"
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

(*lemma "pred1 b b0 (i1::'a) (i2::'a) f P (k::nat) = (
\<forall>m. (m \<le> RRange b & size m=k)\<longrightarrow> (P(m + onemember2 b0 (card (Domain b)+1-k))=
(1/(card (Domain b)+2))*f ((Domain b \<union> {i1,i2})\<times>{b0})))" using lll67d *)

end
