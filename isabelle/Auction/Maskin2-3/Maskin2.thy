theory Maskin2

imports

Maskin2_r2l
Maskin2_l2r_stage2

begin

abbreviation intersectioncondition where "intersectioncondition a w (a1::allocation) a2 i == 
(a1<=a2 & Range a \<subseteq> {a1, a2} & (\<forall> b\<in>Domain a. (b,,i>w(b--i) \<longrightarrow> a,,b=a2) & (b,,i<w(b--i) \<longrightarrow> a,,b=a1)))"

lemma lll96: assumes "intersectioncondition a w a1 a2 i" 
"cartesian (Domain a) b i" 
"b \<in> Domain a" 
"runiq a" 
shows "pseudomax a (w (b--i)) b i"
proof -
  let ?w="w (b--i)" let ?a="a,,b" 
  have "?a \<in> Range a" using assms by (metis eval_runiq_in_Range) then
  have "(?a=a1 \<or> ?a=a2) & a1 \<le> a2" using assms by blast then have 
  3: "a1 <= ?a & a2 >= ?a" by fast
  then have "a1 = ?a \<or> a1 \<le> ?a" by fast
  then have "a1 <= ?a" 
  (*MC: if I remove explicit typing of a1 in definition of intersectioncondition, 
  then here sledgehammer-E says "unprovable"!*)
  by fast
  {
    fix ww let ?bw="b+<(i,ww)" let ?aw="a,,?bw" have
    1: "?bw,,i=ww" using ll50b by fastforce
    have "?bw--i=b--i" (* MC: worth to be singled out as a general lemma, see lll91 *) using
    Domain_empty Domain_insert fst_conv ll19 by (metis Un_absorb) then
    have "w(?bw--i)=?w" by presburger then have 
    0: "(?bw,,i > ?w \<longrightarrow> ?aw=a2) & (?bw,,i < ?w \<longrightarrow> ?aw=a1)" using assms by force
    {
      assume "ww<?w" then have "?bw,,i<?w" using 1 by presburger
      then have "?aw=a1" using 0 by fast then
      have "?a >= ?aw" using 3 by fastforce
    }
    then have 
    2: "ww<?w \<longrightarrow> ?a >= ?aw" by fast
    {
      assume "ww>?w" then have "?bw,,i>?w" using 1 by presburger
      then have "?aw=a2" using 0 by fast then have "?a <= ?aw" using 3 by fast
    }
    then have "(ww<?w \<longrightarrow> ?a >= ?aw) & (ww>?w \<longrightarrow> ?a <= ?aw)" using 2 by fast
  }
  then show ?thesis by fast
qed

lemma lm01: assumes "intersectioncondition a w a1 a2 i" 
"\<forall>b\<in> Domain a \<inter> Domain p. cartesian (Domain a) b i"  "genvick a p i w" "runiq a" shows "dom4 i a p"
proof -
let ?d=Domain
{
  fix b assume 
  0: "b \<in> ?d a \<inter> ?d p" then have "cartesian (?d a) b i" using assms(2) by blast
  then have "pseudomax a (w (b--i)) b i" using lll96 assms 0 IntE by (metis(no_types))
}
thus ?thesis using lll90 assms(3) by auto
qed

lemma lll95: assumes "intersectioncondition a (w::_=>price) a1 a2 i" "cartesian (Domain a) b i"
"runiq a" shows "weakefficient a i b (w (b--i)) a1 a2" 
proof -
  let ?M="w (b--i)" let ?d=Domain obtain w1 w2 where 
  0: "w1 ----> ?M & w2 ----> ?M & (\<forall>j. w1 j < ?M & w2 j > ?M)" using ll29 by presburger
  {
    fix j let ?b1="b+<(i, w1 j)" let ?b2="b+<(i, w2 j)"
    have "?b1,,i = w1 j & ?b2,,i=w2 j" using ll50b by force
    then have "?b1,,i < ?M & ?b2,,i > ?M" using 0 by presburger
    moreover have "?M = w (?b1--i) & ?M = w (?b2 -- i)" using lll91c by metis
    moreover have "?b1\<in>?d a & ?b2\<in>?d a" using assms by force
    ultimately have "a,,?b1=a1 & a,,?b2=a2" using 0 assms(1) by metis
    moreover have "?b1 \<in> Domain a & ?b2 \<in> Domain a" using assms(2) by force
    ultimately have "a``{?b1}={a1} & a``{?b2}={a2}" using assms(3) by (metis Image_runiq_eq_eval)
  }
  then have "(%j. (a``{b+<(i, w1 j)})) = (%j. ({a1})) & 
  (%j. (a``{b+<(i, w2 j)})) = (%j. ({a2}))" by force
  then show ?thesis using 0 weakefficient_def lll89 by fastforce
qed

corollary lll97: assumes "runiq a" "runiq p" "Domain a \<subseteq> Domain p" "functional (Domain a)"
"cartesian (Domain a) b0 i"
"intersectioncondition a w a1 a2 i"
"dom4 i a p" "b \<in> {b0+<(i,v)| (v::price) . True}"
shows
"((a,,b=a1) \<longrightarrow> (p,,b=reducedprice p i a,,(Domain b, b outside {i}, a1))) & 
((a,,b=a2) \<longrightarrow> (p,,b = (w (b--i))*(a2-a1) + 
(reducedprice p i a ,, (Domain b, b outside {i}, a1))))"
proof -
  let ?B="{b0+<(i,v)| (v::price) . True}" let ?d=Domain obtain y where 
  3: "b=b0 +< (i,y)" using assms by blast
  have "i \<in> Domain b" using 3 paste_def by auto moreover have 
  "cartesian (Domain a) b i" using 3 assms(5) lll93c by metis
  then moreover have "weakefficient a i b (w (b--i)) a1 a2" using lll95 assms(1) assms(6) by metis
  ultimately show ?thesis using assms ll31b 3 by simp
qed

corollary lll97b: assumes "runiq a" "runiq p" "Domain a \<subseteq> Domain p" "functional (Domain a)"
"cartesian (Domain a) b0 i"
"intersectioncondition a w a1 a2 i"
"dom4 i a p" shows
"\<forall>b\<in>{b0+<(i,v)| (v::price) . True}.
( ((a,,b=a1) \<longrightarrow> (p,,b=reducedprice p i a,,({i} \<union> Domain (b--i), b outside {i}, a1))) & 
((a,,b=a2) \<longrightarrow> (p,,b = (w (b--i))*(a2-a1) + 
(reducedprice p i a ,, ({i} \<union> Domain (b--i), b outside {i}, a1)))))" using assms lll97 
proof -
let ?B="{b0+<(i,v)| (v::price) . True}" let ?d=Domain
{
  fix b assume "b\<in>?B" 
then moreover have "?d b = {i} \<union> ?d (b--i)" using paste_def Outside_def by fastforce
ultimately have 
  "( ((a,,b=a1) \<longrightarrow> (p,,b=reducedprice p i a,,({i} \<union> ?d (b--i), b outside {i}, a1))) & 
  ((a,,b=a2) \<longrightarrow> (p,,b = (w (b--i))*(a2-a1) + 
  (reducedprice p i a ,, ({i} \<union> ?d (b--i), b outside {i}, a1)))))" using assms lll97 by presburger
}
thus ?thesis by blast
qed

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
  have "g,,xx = (?fx-f1)*(?g xx)/(f2-f1) + (?fx-f2)*?g1/(f1-f2)" 
  using assms by (rule lll92) moreover have "...=
  (?fx-f1)*((?g xx)/(f2-f1)) + (?fx-f2)*?g1/(f1-f2)" by auto moreover have "... = 
  ?fx*((?g1+?g2)/(f2-f1)) - f1*(?g1+?g2)/(f2-f1) + (?fx-f2)*(?g1/(f1-f2))" by algebra moreover have "... = 
  (?fx*?g1/(f2-f1) + ?fx*?g2/(f2-f1) - f1*(?g1+?g2)/(f2-f1)) + (?fx-f2)*(?g1/(f1-f2))" 
  by algebra moreover have "... = 
  (?fx*?g1/(f2-f1) + ?fx*?g2/(f2-f1) - f1*(?g1+?g2)/(f2-f1)) + (?fx*(?g1/(f1-f2)) - f2*(?g1/(f1-f2)))" 
  using lll62 by presburger moreover have "... = 
  ?fx*?g1/(f2-f1) + ?fx*?g1/(-(f2-f1)) + ?fx*?g2/(f2-f1) - f1*(?g1+?g2)/(f2-f1) - f2*(?g1/(f1-f2))" 
  by force moreover have "... = 
  ?fx*?g1/(f2-f1) - ?fx*?g1/(f2-f1) + ?fx*?g2/(f2-f1) - f1*(?g1+?g2)/(f2-f1) - f2*(?g1/(f1-f2))" 
  by linarith moreover have "... = 
  ?fx*?g2/(f2-f1) - f1*((?g1+?g2)/(f2-f1)) - f2*(?g1/(f1-f2))" 
  by force moreover have "... = 
  ?fx*?g2/(f2-f1) - (f1*?g1/(f2-f1) + f1*?g2/(f2-f1)) - f2*?g1/(f1-f2)" by algebra moreover have "... = 
  ?fx*?g2/(f2-f1) - f1*?g1/(-(f1-f2)) - f1*?g2/(f2-f1) - f2*?g1/(f1-f2)" by force moreover have "... = 
  ?fx*?g2/(f2-f1) + f1*(?g1/(f1-f2)) - f1*(?g2/(f2-f1)) - f2*(?g1/(f1-f2))"  
  by (metis (hide_lams, mono_tags) diff_minus_eq_add minus_divide_right times_divide_eq_right) moreover have "... =
  ?fx*(?g2/(f2-f1)) + (f1*(?g1/(f1-f2)) - f2*(?g1/(f1-f2))) - f1*(?g2/(f2-f1))"
  by algebra moreover have "... = 
  ?fx*(?g2/(f2-f1)) + (f1-f2)*(?g1/(f1-f2)) - f1*(?g2/(f2-f1))" using lll62 by presburger moreover have "... = 
  (?fx*(?g2/(f2-f1)) - f1*(?g2/(f2-f1))) + (f1-f2)*(?g1/(f1-f2))" by algebra moreover have "... = 
  (?fx-f1)*(?g2/(f2-f1)) + (f1-f2)*(?g1/(f1-f2))" using lll62 by presburger moreover have "... = 
  (?fx-f1)*?g2/(f2-f1) + ?g1*((f1-f2)/(f1-f2))" by simp moreover have "... = 
  (?fx-f1)*?g2/(f2-f1) + ?g1*1" using assms by force ultimately show ?thesis by linarith
qed

corollary lll92c: assumes "xx \<in> X \<inter> (f^-1)``{f1,f2}" "f1 \<noteq> f2" "runiq f"
"\<forall>x \<in> X. (((f,,x=(f1::real)) \<longrightarrow> (g,,x=(g1 x))) & ((f,,x=f2) \<longrightarrow> (g,,x=(g1 x)+(g2 x))))" 
shows "g,,xx = (f,,xx - f1)*(g2 xx)/(f2-f1) + (g1 xx)" using assms lll92b 
proof -
have 4: "\<forall>x \<in> X. (((f,,x=(f1::real)) \<longrightarrow> (g,,x=(g1 x))) & ((f,,x=f2) \<longrightarrow> (g,,x=(%x. ((g1 x)+(g2 x))) x)))"
using assms(4) by blast
show ?thesis using assms(1,2,3) 4 by (rule lll92b)
qed

corollary lll98: assumes "bb \<in> {b0+<(i,v)| (v::price) . True} \<inter> (a^-1)``{a1,a2}" "a1 \<noteq> a2" 
"runiq a" "runiq p" "Domain a \<subseteq> Domain p" "functional (Domain a)"
"cartesian (Domain a) b0 i"
"intersectioncondition a w a1 a2 i"
"dom4 i a p"
"g1=(%b. reducedprice p i a ,, ({i} \<union> Domain (b--i), b--i, a1))"
"g2=(%b. (w (b--i))*(a2-a1))"
shows
"p,,bb = (a,,bb - a1)*(g2 bb)/(a2-a1) + (g1 bb)"
proof -
  let ?g1="%b. reducedprice p i a ,, ({i} \<union> Domain (b--i), b outside {i}, a1)" let ?g2="%b. (w (b--i))*(a2-a1)"
  let ?B="{b0+<(i,v)| (v::price) . True}"
  have "\<forall>b \<in> ?B.(
  ( ((a,,b=a1) \<longrightarrow> (p,,b=reducedprice p i a,,({i} \<union> Domain (b--i), b outside {i}, a1))) & 
  ((a,,b=a2) \<longrightarrow> (p,,b = (w (b--i))*(a2-a1) + 
  (reducedprice p i a ,, ({i} \<union> Domain (b--i), b outside {i}, a1))))))" 
  using assms(3,4,5,6,7,8,9) lll97b by presburger 
  then have "\<forall>b \<in> ?B.(( ((a,,b=a1) \<longrightarrow> (p,,b=(?g1 b))) & 
  ((a,,b=a2) \<longrightarrow> (p,,b = ?g2 b + (?g1 b)))))" by fast
  moreover have "?g1=g1 & ?g2=g2" using assms by fast ultimately have 
  4: "\<forall>b \<in> ?B.(( ((a,,b=a1) \<longrightarrow> (p,,b=(g1 b))) & ((a,,b=a2) \<longrightarrow> (p,,b = (g1 b) + (g2 b)))))" by fastforce
  show ?thesis using assms(1,2,3) 4 by (rule lll92c)
qed

corollary lll98b: assumes "b \<in> {b0+<(i,v)| (v::price) . True} \<inter> (a^-1)``{a1,a2}" "a1 \<noteq> a2" 
"runiq a" "runiq p" "Domain a \<subseteq> Domain p" "functional (Domain a)"
"cartesian (Domain a) b0 i"
"intersectioncondition a w a1 a2 i"
"dom4 i a p"
"g1=(%x. reducedprice p i a ,, ({i} \<union> Domain x, x, a1))"
shows "p,,b = (a,,b - a1)*(w (b--i)) + (g1 (b--i))" using assms lll98 by auto

corollary lm02: assumes "\<forall> b\<in>Domain a. cartesian (Domain a) b i & runiq (b||{i}) & i \<in> Domain b" 
"Domain a \<subseteq> (a^-1)``{a1, a2}" "a1 \<noteq> a2" "runiq a" "runiq p" "Domain a \<subseteq> Domain p"
"functional (Domain a)" "intersectioncondition a w a1 a2 i" "dom4 i a p"
shows
"genvick a p i w"
proof -
let ?d=Domain let ?u=runiq let ?g1="%x. reducedprice p i a ,, ({i} \<union> Domain x, x, a1)" 
let ?X="(% b. b outside {i})`(?d a)"
{
  fix b assume 
  1: "b\<in> ?d a \<inter> (?d p)" then have
  0: "cartesian (?d a) b i & ?u (b||{i}) & i \<in> ?d b" using assms by auto
  have "b = b +* {i}\<times>(b``{i})" by (metis ll84)
  moreover have "b``{i}=(b||{i})``{i}" using lll99 by (metis Diff_empty)
  moreover have "... = {(b||{i}),,i}" using 0  
  by (metis Image_runiq_eq_eval Image_within_domain' calculation(2))
  moreover have "... = {b,,i}" by (metis calculation(2) eval_rel.simps)
  ultimately have "b= b +* {i}\<times>{b,,i}" by metis
  then have "b \<in> {b+<(i,v)| v. True} \<inter> (a^-1)``{a1, a2}" using 1 assms by auto
  then have "p,,b = (a,,b - a1)*(w (b--i)) + (?g1 (b--i))" using assms lll98b 0 by presburger
}
then have "\<forall>b \<in> ?d a \<inter> (?d p). (p,,b = (w (b--i))*(a,,b - a1) + (?g1 (b--i)))" by simp 
thus ?thesis by fast
qed

theorem th10: assumes "\<forall> b\<in>Domain a. cartesian (Domain a) b i & 
runiq (b||{i}) (* MC: this is implied by functional (Domain a) below *)
& i \<in> Domain b" 
"Domain a \<subseteq> (a^-1)``{a1, a2}" "a1 \<noteq> a2" "runiq a" "runiq p" "Domain a \<subseteq> Domain p"
"functional (Domain a)" "intersectioncondition a w a1 a2 i" shows 
"genvick a p i w = dom4 i a p"
proof -
  have "dom4 i a p \<longrightarrow> genvick a p i w" using lm02 assms by auto
  moreover have "\<forall>b\<in>Domain a \<inter> Domain p. cartesian (Domain a) b i" using assms(1) by blast
  ultimately show ?thesis using lm01 assms(4,8) by metis
qed

end

