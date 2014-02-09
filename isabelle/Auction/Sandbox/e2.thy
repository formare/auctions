theory e2

imports e

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
  then have "v*?a - ?k*(?a - a1) <= v*?av - ?k*(?av - a1)" by (smt e2.ll57)
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
  then have "pseudomax a (w (b--i)) b i" using lll96 assms 0 by (smt IntE fst_conv snd_conv)
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

corollary lll98: assumes "bb \<in> {b0+<(i,v)| (v::price) . True} \<inter> (a^-1)``{a1,a2}" "a1 \<noteq> a2" 
"runiq a" "runiq p" "Domain a \<subseteq> Domain p" "functional (Domain a)"
"cartesian (Domain a) b0 i"
"intersectioncondition a w a1 a2 i"
"dom4 i a p"
"g1=(%b. reducedprice p i a ,, ({i} \<union> Domain (b--i), b--i, a1))"
"g2=(%b. (w (b--i))*(a2-a1))"
shows
"p,,bb = (a,,bb - a1)*(g2 bb)/(a2-a1) + (g1 bb)"
using assms lll97b lll92b
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
  4: "\<forall>b \<in> ?B.(( ((a,,b=a1) \<longrightarrow> (p,,b=(g1 b))) & ((a,,b=a2) \<longrightarrow> (p,,b = g2 b + (g1 b)))))" by blast
  show ?thesis using assms(1,2,3) 4 lll92b by smt
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
let ?X="(% b. Outside b {i})`(?d a)"
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

corollary assumes "\<forall> b\<in>Domain a. cartesian (Domain a) b i & 
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

