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

theory Maskin2_r2l

imports 
Real_Vector_Spaces
Maskin2_l2r_stage1

begin

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

lemma ll57: (*repetition*) fixes a::real fixes b c shows "a*b - a*c=a*(b-c)"
using assms by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

lemma lll62: fixes a::real fixes b c shows "a*b - c*b=(a-c)*b" (*MC: repetition*)
using assms ll57 by (metis comm_semiring_1_class.normalizing_semiring_rules(7))

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







section {* Maskin2<= *}

abbreviation pseudomax where "pseudomax a w b i == 
(\<forall>ww. (ww < w \<longrightarrow> (a,,b \<ge> a,,(b +< (i,ww)))) & (ww > w \<longrightarrow> (a,,b \<le> a,,(b +< (i,ww)))))"

lemma lll87: assumes "pseudomax a k b i" shows
"((v::price)*(a,,b)) - (k*(a,,b)) <= v*(a,,(b+<(i,v))) - (k*(a,,(b+<(i,v))))"
proof -
  let ?bv="b+<(i,v)" let ?d="v-k" let ?a="a,,b" let ?av="a,,?bv" let ?lh="?d * ?a" let ?rh="?d*?av"
  {
    assume "v>k" then have 
    "((v-k)>0) & (a,,b \<le> a,,?bv)" using assms by force
    then have "(v-k)*(a,,b) <= (v-k)*(a,,?bv)" by (metis real_mult_le_cancel_iff2)
  }
  then have 
  0: "v>k \<longrightarrow> ?lh <= ?rh" by fast
  {
    assume "v<k" then have 
    "((v-k)<0) & (a,,b >= a,,?bv)" using assms by force
    then have "(v-k)*(a,,b) <= (v-k)*(a,,?bv)" by (metis (full_types) mult_left_mono_neg sup.semilattice_strict_iff_order)
  }
  then have "v<k \<longrightarrow> ?lh <= ?rh" by fast
  moreover have "v=k \<longrightarrow> (v-k)*(a,,b) <= (v-k)*?av" by simp
  ultimately have "?lh <= ?rh" using 0 by linarith 
  moreover have "?lh=v*?a - (k*?a)" by (metis 
  comm_semiring_1_class.normalizing_semiring_rules(7) ll57)
  moreover have "?rh=(v*?av) - (k*?av)" using lll62 by presburger
  ultimately show "(v*?a) - (k*?a) <= (v*?av) - (k*?av)" by simp
qed

abbreviation genvick where "genvick a p i w ==
(EX (a1::allocation) t. (\<forall> b \<in> Domain a \<inter> (Domain p). p,,b=w (b--i)*(a,,b - a1) + (t (b--i))))"

(*
lemma lll91: assumes "Domain Q \<subseteq> X" shows "P outside X = (P +* Q) outside X"
using assms Outside_def paste_def paste_outside_restrict l38 lll72 
Domain_empty Domain_insert Un_insert_left Un_insert_right fst_conv insert_def ll19 singleton_conv
by (metis Diff_subset_conv ll18 ll52 outside_reduces_domain subset_empty sup_bot.left_neutral sup_commute)
*)

lemma lll88: assumes "genvick a p i w" "pseudomax a (w (b--i)) b i" "b \<in> Domain a \<inter> (Domain p)"
"b+<(i,v) \<in> Domain a \<inter> (Domain p)"
shows "(v::price)*(a,,b) - (p,,b) <= v*(a,,(b +< (i,v))) - p,,(b+<(i,v))"
proof -
  let ?bv="b+<(i,v)" let ?a="a,,b" let ?av="a,,?bv" let ?p="p,,b" let ?pv="p,,?bv"
  let ?k="w (b--i)" let ?d=Domain obtain a1 t where 
  0: "(\<forall> b \<in> ?d a \<inter> ?d p. p,,b=w (b--i)*(a,,b - a1) + (t (b--i)))" using assms(1) by blast
  have "v*?a - ?k*?a <= v*?av - ?k*?av" using lll87 assms(2) by fast
  then have "v*?a - ?k*(?a - a1) <= v*?av - ?k*(?av - a1)" by (smt ll57)
  then have "v*?a - ?k*(?a - a1) - t (b--i) <= v*?av - ?k*(?av - a1) - t (b--i)" by smt
  then have "v*?a - (?k*(?a - a1) + t (b--i)) <= v*?av - (?k*(?av - a1) + t (b--i))" by force
  moreover have "b -- i = ?bv -- i" (* MC: worth to be singled out as general lemma, see lll91 *) by (smt 
  Domain_empty Domain_insert Un_insert_left Un_insert_right fst_conv insert_def ll19 singleton_conv)
  moreover have "?bv \<in> ?d a \<inter> ?d p" using assms by simp
  ultimately show ?thesis using assms 0 by metis
qed

corollary lll90: assumes "genvick a p i w" 
"\<forall>b\<in>Domain a \<inter> Domain p. (pseudomax a (w (b--i)) b i)"
shows "dom4 i a p" using dom4_def assms lll88 lll89 
proof -
  let ?d=Domain 
  {
    fix b::bid fix v let ?bv="b+<(i,v)" assume "{b, ?bv} \<subseteq> ?d a \<inter> ?d p & i \<in> ?d b"
    then moreover have "pseudomax a (w (b--i)) b i" using assms by auto ultimately have 
    "(v::price)*(a,,b) - (p,,b) <= v*(a,,(b +< (i,v))) - p,,(b+<(i,v))" using lll88 assms 
    by (metis insert_subset surjective_pairing)
  }
  then show ?thesis using dom4_def by force
qed

corollary lll90a: assumes "\<forall>b \<in> Domain a \<inter> Domain p. (pseudomax a (w (b--i)) b i)" shows
"genvick a p i w \<longrightarrow> dom4 i a p" using assms lll90 by blast

















section {* Merging Maskin2=> and Maskin2<= *}

end

