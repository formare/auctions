theory Scraps2

imports Main "../StrictCombinatorialAuction" "../MiscTools" "../Universes"
"../UniformTieBreaking"

begin

lemma lm07: assumes "isChoice (graph {winningAllocationsRel N G b} t)" shows 
"t (winningAllocationsRel N G b) \<in> winningAllocationsRel N G b" 
using assms
proof - (* MC: to be cleaned *)
let ?W="winningAllocationsRel N G b" let ?T="graph {?W} t" let ?TT="graph UNIV t" let ?TTT="Graph t"
have "?T``{?W} \<subseteq> ?W" using assms by fast
moreover have "?TTT``{?W} = (?TTT || {?W})``{?W}" using restrict_def Image_def by fast
moreover have "?TTT || {?W} = ?TT || {?W}" using ll36 by metis
moreover have "... = ?T" using lm05 by (metis Int_UNIV_left)
moreover have "?T``{?W} = ?TTT``{?W}" using lm06 by (metis calculation(2))
moreover have "?T``{?W} \<subseteq> t`{?W}" using l4 by (metis calculation(5) subsetI)
ultimately show ?thesis using assms by (metis (hide_lams, no_types) image_eqI insertI1 l4 set_rev_mp)
qed

corollary lm53b: assumes "condition1 (b::_ => real) i"  "a \<in> possibleAllocationsRel N G" 
"i\<in>N-{n}" "n \<in> Domain a" "finite N" "finite G"
shows
"alpha N G b n \<ge> setsum b (a -- n)" (is "?L \<ge> ?R") using assms lm53 
proof -
let ?X="{n}" have "Domain a \<inter> ?X \<noteq> {}" using assms by blast
then show "Max ((setsum b)`(possibleAllocationsRel (N-?X) G)) \<ge> setsum b (a outside ?X)" using assms lm53 by metis
qed

lemma lm60: assumes "n \<notin> Domain a" "a \<in> possibleAllocationsRel N G" "finite G" "finite N" shows 
"alpha N G b n \<ge> setsum b (a -- n)"
proof -
let ?a="a -- n" let ?d=Domain have "?a = a" using assms Outside_def by blast
then moreover have "?d ?a \<subseteq> N-{n}" using 
assms(1,2) lm28b by (metis insert_Diff_single subset_insert)
ultimately have "a \<in> possibleAllocationsRel (N-{n}) G" using assms 
by (metis (full_types) lm28b)
then have "setsum b a \<in> (setsum b ` (possibleAllocationsRel (N-{n}) G))"
by blast
moreover have "finite (possibleAllocationsRel (N-{n}) G)" using assms lm59 by (metis finite_Diff)
ultimately show ?thesis using Max.coboundedI
by (metis (hide_lams, no_types) `a -- n = a` finite_imageI)
qed

corollary lm61: (*MC: of lm60 and lm53b*) assumes
"condition1 (b::_ => real) i" 
"a \<in> possibleAllocationsRel N G"
"i\<in>N-{n}"
"finite N"
"finite G"
shows "alpha N G b n \<ge> setsum b (a -- n)" using assms lm53b lm60 by metis

corollary lm61b: assumes "condition1 (b::_ => real) i" "a \<in> winningAllocationsRel N G c" 
"i\<in>N-{n}" "finite N" "finite G" shows "alpha N G b n \<ge> setsum b (a -- n)"  
proof -
have "a \<in> possibleAllocationsRel N G" using assms(2) lm03 by fast
then show ?thesis using assms lm61 by metis
qed

corollary lm61c: assumes "condition1 (b::_ => real) i" "i\<in>N-{n}" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows 
"alpha N G b n \<ge> remainingValueRel N G t b n" (is "?L \<ge> ?R") 
using assms lm03 lm61 lm07 set_rev_mp 
proof -
have "winningAllocationRel N G t b \<in> winningAllocationsRel N G b" 
using assms(5) lm07 by (metis (hide_lams, no_types))
then show ?thesis using lm61b assms by metis
qed

lemma lm62: "(a::real) \<ge> b = (a - b \<ge> 0)" by linarith

(*
lemma lm72b: assumes "t (winningAllocationsRel N G b) \<in> winningAllocationsRel N G b" shows
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))" using assms lm72 
by blast
*)

corollary lm61d: assumes "condition1 (b::_=>real) i" "i\<in>N-{n}" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows "paymentsRel N G t b n \<ge> 0" 
proof - have "alpha N G b n \<ge> remainingValueRel N G t b n" using assms lm61c by metis thus ?thesis using lm62 by simp qed

abbreviation "condition2 b N == EX i1 i2. (i1 \<in> N - {i2} & i2 \<in> N - {i1} & condition1 b i1 & condition1 b i2)"

corollary lm61e:
assumes 
"condition2 (b::_=>real) N" 
"finite N"
"finite G"
"isChoice (graph {winningAllocationsRel N G b} t)"
shows
"paymentsRel N G t b n \<ge> 0"
proof -
  obtain i where 
  0: "condition1 b i & i \<in> N-{n}" using assms(1) by blast
  then have "condition1 b i" by blast moreover have "i \<in> N-{n}" using 0 by fast 
  moreover have "finite N" using assms(2) by simp moreover have "finite G" using assms(3) by auto  
  moreover have "isChoice (graph {winningAllocationsRel N G b} t)" using assms(4) by fast  
  ultimately show ?thesis by (rule lm61d)
qed

abbreviation "monotonebids == condition2"

lemma lm71: fixes N b assumes
"EX i1 i2. i1 \<in> N - {i2} & i2 \<in> N - {i1} & 
(\<forall> t t'. (trivial t & trivial t' & Union t \<subseteq> Union t') \<longrightarrow>
setsum b ({i1}\<times>t) \<le> setsum b ({i1}\<times>t') & setsum b ({i2}\<times>t) \<le> setsum b ({i2}\<times>t'))"
shows "condition2 (b) N" using assms by blast

corollary lm61f: assumes "monotonebids (b::_=>real) N" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows "\<forall>n. paymentsRel N G t b n \<ge> 0"  
proof -
{fix n have "paymentsRel N G t b n \<ge> 0" using assms by (rule lm61e)} then show ?thesis by fastforce
qed

lemma ll59: shows "P O Q={(x,z) | x z. (EX y. (x,y) \<in> P & (y,z)\<in>Q)}"
using assms relcomp_def by blast

lemma ll60: shows "P O Q O R = 
{(v,z)| v z. EX x y. (v,x) \<in> P & (x,y) \<in> Q & (y,z)\<in>R}" by blast

lemma ll88: assumes "P xx" shows "{(x, f x)|x. P x}``{xx} = {f xx}"
using Image_def assms by blast

lemma lll07: "(P \<inter> Q)``{x} = (P``{x} \<inter> (Q``{x}))" by fastforce

lemma assumes "P \<inter> Q={}" shows "P^-1 \<inter> Q^-1={}" using assms by fast

end

