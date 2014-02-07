theory e2

imports e

begin

lemma ll57: (*repetition*) fixes a::real fixes b c shows "a*b - a*c=a*(b-c)"
using assms by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

lemma lll62: fixes a::real fixes b c shows "a*b - c*b=(a-c)*b" (*MC: repetition*)
using assms ll57 by (metis comm_semiring_1_class.normalizing_semiring_rules(7))

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
(EX a1 t. (\<forall> b. p,,b=w (b--i)*(a,,b - a1) + (t,,(b--i))))"

(*
lemma lll91: assumes "Domain Q \<subseteq> X" shows "P outside X = (P +* Q) outside X"
using assms Outside_def paste_def paste_outside_restrict l38 lll72 
Domain_empty Domain_insert Un_insert_left Un_insert_right fst_conv insert_def ll19 singleton_conv
by (metis Diff_subset_conv ll18 ll52 outside_reduces_domain subset_empty sup_bot.left_neutral sup_commute)
*)

corollary lll91b: "(P +* Q) outside (Domain Q)=P outside (Domain Q)" using ll19 by (metis Un_absorb)

corollary lll91c: "(P +< (x,y)) -- x = P -- x" using lll91b by (metis Domain_empty Domain_insert fst_conv)

lemma lll89: "P +< (x,y) = P +* {x}\<times>{y}" by simp

corollary ll50b: "(P +* ({x}\<times>{y})),,x=y"
proof -
  let ?f="{x}\<times>{y}" let ?d=Domain have "?d ?f={x}" by simp 
  then have "(P +* ?f)``{x}=?f``{x}" using ll50 subset_refl inf_absorb2 by metis
  moreover have "...={y}" by fast ultimately show ?thesis by simp
qed

lemma lll88: assumes "genvick a p i w" "pseudomax a (w (b--i)) b i"
shows "(v::price)*(a,,b) - (p,,b) <= v*(a,,(b +< (i,v))) - p,,(b+<(i,v))"
proof -
  let ?bv="b+<(i,v)" let ?a="a,,b" let ?av="a,,?bv" let ?p="p,,b" let ?pv="p,,?bv"
  let ?k="w (b--i)" obtain a1 t where 
  0: "(\<forall> b. p,,b=w (b--i)*(a,,b - a1) + (t,,(b--i)))" using assms(1) by blast
  have "v*?a - ?k*?a <= v*?av - ?k*?av" using lll87 assms(2) by fast
  then have "v*?a - ?k*(?a - a1) <= v*?av - ?k*(?av - a1)" by (smt e2.ll57)
  then have "v*?a - ?k*(?a - a1) - t,,(b--i) <= v*?av - ?k*(?av - a1) - t,,(b--i)" by smt
  then have "v*?a - (?k*(?a - a1) + t,,(b--i)) <= v*?av - (?k*(?av - a1) + t,,(b--i))" by force
  moreover have "b -- i = ?bv -- i" (* MC: worth to be singled out as general lemma, see lll91 *) by (smt 
  Domain_empty Domain_insert Un_insert_left Un_insert_right fst_conv insert_def ll19 singleton_conv)
  ultimately show ?thesis by (metis "0")
qed

corollary lll90: assumes "genvick a p i w" "\<forall>b. (pseudomax a (w (b--i)) b i)"
shows "dom4 i a p" using dom4_def assms lll88 lll89 by metis

corollary lll90a: assumes "\<forall>b. (pseudomax a (w (b--i)) b i)" shows
"genvick a p i w \<longrightarrow> dom4 i a p" using assms lll90 by blast

section {* Merging Maskin2=> and Maskin2<= *}

abbreviation intersectioncondition where "intersectioncondition a w (a1::allocation) a2 i == 
(a1<=a2 & Range a \<subseteq> {a1, a2} & (\<forall> b. (b,,i>w(b--i) \<longrightarrow> a,,b=a2) & (b,,i<w(b--i) \<longrightarrow> a,,b=a1)))"

lemma assumes "intersectioncondition a (w::_=>price) a1 a2 i" "cartesian (Domain a) b i"
"runiq a" shows 
"weakefficient a i b (w (b--i)) a1 a2" 
proof -
let ?M="w (b--i)" obtain w1 w2 where 
0: "w1 ----> ?M & w2 ----> ?M & (\<forall>j. w1 j < ?M & w2 j > ?M)" using ll29 by presburger
{
  fix j let ?b1="b+<(i, w1 j)" let ?b2="b+<(i, w2 j)"
  have "?b1,,i = w1 j & ?b2,,i=w2 j" using ll50b by force
  then have "?b1,,i < ?M & ?b2,,i > ?M" using 0 by presburger
  moreover have "?M = w (?b1--i) & ?M = w (?b2 -- i)" using lll91c by metis
  ultimately have "a,,?b1=a1 & a,,?b2=a2" using 0 assms(1) by fastforce
  moreover have "?b1 \<in> Domain a & ?b2 \<in> Domain a" using assms(2) cartesian_def by force
  ultimately have "a``{?b1}={a1} & a``{?b2}={a2}" using assms(3) by (metis Image_runiq_eq_eval)
}
then have "(%j. (a``{b+<(i, w1 j)})) = (%j. ({a1})) & 
(%j. (a``{b+<(i, w2 j)})) = (%j. ({a2}))" by force
then show ?thesis using 0 weakefficient_def lll89 by fastforce
qed

lemma assumes "intersectioncondition a w a1 a2 i" shows "pseudomax a (w (b--i)) b i"
proof -
let ?w="w (b--i)" let ?a="a,,b" have "(?a=a1 \<or> ?a=a2) & a1 \<le> a2" sorry then have 
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
  0: "(?bw,,i > ?w \<longrightarrow> ?aw=a2) & (?bw,,i < ?w \<longrightarrow> ?aw=a1)" using assms by presburger
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

end

