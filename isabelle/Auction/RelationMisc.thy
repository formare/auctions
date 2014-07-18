(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Results involving relations along with objects from other theories, as reals or partitions *}

theory RelationMisc

imports
  Main
  RelationProperties
  Real
  Real_Vector_Spaces
  Partitions (*MC: needed for ll76 *)

begin

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
  then have "f``{xx} \<subseteq> {f1,f2}" using assms(3) ll71b by metis then have 
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


lemma ll76: assumes "is_partition XX" shows "trans (part2rel XX)" 
proof -
let ?f=part2rel let ?R="?f XX"
{
  fix x y z assume "(x,y) \<in> ?R" then obtain X1 where 
  1: "X1\<in>XX & x\<in>X1 & y\<in>X1" using ll73 by metis 
  assume "(y,z)\<in>?R" then obtain X2 where 
  2: "X2\<in>XX & y\<in>X2 & z\<in>X2" using ll73 by metis
  have "{y} \<subseteq> X1 \<inter> X2" using 1 2 by fast
  hence "X1=X2" using assms 1 2 by (metis empty_iff is_partition_def singleton_iff subset_empty)
  hence "(x,z)\<in>?R" using ll73 1 2 by fast
}
thus ?thesis using trans_def by blast
qed

lemma ll72: assumes "runiq f" shows "is_partition {f^-1 `` {y}| y. y\<in> Range f}" 
proof -
let ?i=is_partition let ?R=Range let ?r=runiq let ?g="f^-1"
let ?P="{?g `` {y}| y. y\<in> ?R f}" have "?thesis = (\<forall> X\<in> ?P . \<forall> Y \<in> ?P . (X \<inter> Y \<noteq> {} \<longleftrightarrow> X=Y))" 
using is_partition_def by (rule exE_realizer)
thus ?thesis using ll68 assms by fast 
qed

lemma ll79: assumes "runiq f" shows "kernel f partitions (Domain f)"
proof -
have 0: "Domain f = \<Union> kernel f" using ll65 by blast
have "is_partition (kernel f)" using assms ll72 ll65 by metis
thus ?thesis using 0 is_partition_of_def by metis
qed

lemma ll77: assumes "is_partition XX" shows "equiv (Union XX) (part2rel XX)" 
using assms ll74 ll75 ll76 equiv_def by fast

corollary ll78: assumes "runiq f" shows "equiv (Domain f) (part2rel (kernel f))"
using assms ll77 ll79 is_partition_of_def by metis

lemma lll59: assumes "trivial Y" shows "runiq (X \<times> Y)" using assms 
runiq_def Image_subset ll84 trivial_subset by (metis ll83)

end
