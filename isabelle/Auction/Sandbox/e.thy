theory e

imports d (* SEQ *) Real
Real_Vector_Spaces Limits Conditionally_Complete_Lattices

begin
lemma ll57: fixes a::real fixes b c shows "a*b - a*c=a*(b-c)"
using assms by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

(* MC: From here on we must restrict valuations to numbers *)

lemma ll06: fixes v::price fixes k::allocation 
fixes v1::"nat => price" fixes v2 i a p b 
assumes 
"cartesian (Domain a) b i" 
"cartesian (Domain p) b i"
"i \<in> Domain b" 
"b \<in> Domain a \<inter> (Domain p)" "dom4 i a p" "v1 ----> v" "v2 ----> v"
assumes "(%j . a,, (b +* {i}\<times>{v2 j}) - a,, (b +* {i}\<times>{v1 j})) ----> k" 
shows "(%j. (p,, (b +* {i}\<times>{v2 j}) - (p,, (b +* {i}\<times>{v1 j})))) ----> v*k"
proof -
  (*Proof stub: weak dominance yields
  \<forall>j . v1*[a(b2) - a(b1)] \<le> p(b2)-p(b1) \<le> v2*[a(b2) - a(b1)] 
  Sandwiched btw two sequences both converging to v*k...*)
  let ?D="Domain" let ?I="{i}" 
  let ?b2="%j. (b +* (?I \<times> {v2 j}))"
  let ?b1="%j. (b +* (?I \<times> {v1 j}))"
  let ?e="%j. (a,, (?b2 j) - (a,, (?b1 j)))"
  let ?f="%j. (v1 j)*((a,, (?b2 j)) - (a,, (?b1 j)))"
  let ?g="%j. p,, (?b2 j) - (p,, (?b1 j))"
  let ?h="%j. (v2 j)*((a,, ?b2 j) - (a,, ?b1 j))"
  (*+ and * for functions are defined in ~~/src/HOL/Library/Function_Algebras.thy*)
  have "v1 ----> v & ?e ----> k & ?f=(%j. ((v1 j) * (?e j)))" 
  using assms by fastforce then have 
  10: "?f ----> v * k" by (metis (mono_tags) tendsto_mult)
  have "?e ----> k & ?h=(%j. v2 j * ?e j) & v2 ----> v" using assms by fast hence 
  11: "?h ----> v * k" by (metis (mono_tags) tendsto_mult)
  {
    fix j let ?V1="v1 j" let ?V2="v2 j" 
    let ?Z1="?I \<times> {?V1}" let ?Z2="?I \<times> {?V2}"
    (*let ?B1="?b1 j" let ?B2="?b2 j"*)
    let ?B1="b +* ?Z1" let ?B2="b +* ?Z2" have 
    0: "?D ?Z1 \<subseteq> ?D b & ?D ?Z2 \<subseteq> ?D b" using assms by blast 
    hence 
    1: "?D ?B1 = ?D b" using assms by (metis paste_Domain sup_absorb1) 
    have 
    2: "?D ?B2 = ?D b" using 0 assms by (metis paste_Domain sup_absorb1) 
    (* also have "b \<in> (?D a) & b \<in> ?D p" using assms by blast *)
    have "?B1 \<in> ?D a" using assms cartesian_def by force
    moreover have "?B1 \<in> ?D p" using assms cartesian_def by force
    moreover have "?B2 \<in> ?D a" using assms cartesian_def by force
    moreover have "?B2 \<in> ?D p" using assms cartesian_def by force
    ultimately have 
    "?B1 \<in> ?D a & ?B2 \<in> ?D a & ?B1 \<in> ?D p & ?B2 \<in> ?D p"
    by blast
    hence
    3: "i \<in> ?D ?B1 & i \<in> ?D ?B2 & {?B1, ?B2} \<subseteq> ?D a \<inter> (?D p)" using 1 2 assms by blast
    have "?D ?Z1= ?D ?Z2" by force hence 
    4: "?B1 +* ?Z2=?B2 & ?B2 +* ?Z1=?B1" using ll53 ll56 by (metis subset_refl)
    hence "{?B1, ?B1 +* ?Z2} \<subseteq> ?D a \<inter> (?D p) & i \<in> ?D ?B1" using 3 by presburger
    hence "?V2*(a,, ?B1)-(p,, ?B1) <= ?V2*(a,, (?B1 +* ?Z2))-(p,, (?B1 +* ?Z2))" 
    using assms dom4_def by auto hence 
    "p,, ?B2-(p,, ?B1) \<le> ?V2*(a,, ?B2)-?V2*(a,, ?B1)" using 4 by force hence 
    5: "p,, ?B2 - (p,, ?B1) \<le> ?V2*((a,, ?B2) - (a,, ?B1))" using ll57 by simp
    have "{?B2, ?B2 +* ?Z1} \<subseteq> ?D a \<inter> (?D p) & i \<in> ?D ?B2" using 3 4 by auto hence 
    "?V1*(a,, ?B2) - (p,, ?B2) <= ?V1*(a,, (?B2 +* ?Z1)) - (p,, (?B2 +* ?Z1))"
    using assms dom4_def by auto hence 
    "p,, ?B2 - (p,, ?B1) \<ge> ?V1* (a,, ?B2) - (?V1* (a,, ?B1))" using 4 by force
    hence "p,, ?B2 - (p,, ?B1) \<ge> ?V1 * ((a,, ?B2) - (a,, ?B1))" using ll57 by simp
    hence "v1 j * ((a,, ?b2 j) - (a,, ?b1 j)) \<le> p,, (?b2 j) - (p,, ?b1 j) &
    p,, (?b2 j) - (p,, ?b1 j) \<le> v2 j*((a,, ?b2 j) - (a,, ?b1 j))" using 5 by fast
  }
  hence "\<forall>j. (?f j \<le> ?g j & ?g j \<le> ?h j)" by fast hence 
  "eventually (\<lambda>n. ?f n \<le> ?g n) sequentially & 
  eventually (\<lambda>n. ?g n \<le> ?h n) sequentially" by fastforce hence "?g ----> v*k" 
  using assms real_tendsto_sandwich 10 11 by fast thus ?thesis by force
qed

lemma ll20: fixes a b i assumes "b \<in> Domain a" shows 
"reducedbid i a,,b=(Domain b, b outside {i}, a,,b)"
proof -
  let ?d=Domain let ?f="%x. (?d x, x outside {i}, a,,x)"
  let ?P="%x. x \<in> ?d a" let ?r="{(b, ?f b)| b. ?P b}"
  have "?r,,b=?f b" using assms by (rule l16)
  thus ?thesis using reducedbid_def by presburger
qed

type_synonym valuation=price
(*
type_synonym allocation = "good => participant"
type_synonym valuation = "allocation => price"
type_synonym bid = "(participant \<times> valuation) set"
*)

definition singlepaste where "singlepaste F f = F +* ({fst f} \<times> {snd f})"
notation singlepaste (infix "+<" 75)
value "{(1::nat,3::nat)} +< (1,2)"

(*
definition eff0 where "eff0 
(a::(bid \<times> allocation) set) 
(i::participant) 
(b::bid)
 v 
(a1::allocation) a2 =
(\<exists> v1 v2::(nat => valuation). (
(%j. (a``{b+*({i}\<times>{v1 j})}))=(%j. {a1})
&
(%j. (a``{b+*({i}\<times>{v2 j})})) = (%j. {a2})
&
(%j. v1 j a1) ----> v a1
&
(%j. v1 j a2) ----> v a2
&
(%j. v2 j a1) ----> v a1
&
(%j. v2 j a2) ----> v a2
))"

lemma delme: fixes v::valuation fixes k::allocation 
fixes P::price
fixes v1::"nat => valuation" fixes v2::"nat => valuation" 
fixes i::participant
fixes a::"(bid \<times> allocation) set"  
assumes 
"cartesian (Domain a) b i" 
"cartesian (Domain p) b i"
"i \<in> Domain b" 
"b \<in> Domain a \<inter> (Domain p)" 
"\<forall> v. dom1 i a p v" 
"(%j. ((v1 j) (a,,(b+(i,v2 j)))) - (v1 j)(a,,(b + (i, v1 j)))) ----> P"
"(%j. ((v2 j) (a,,(b+(i,v2 j)))) - (v2 j)(a,,(b + (i, v1 j)))) ----> P"
(*"v1 ----> v" "v2 ----> v"*)
(* assumes "(%j . a,, (b +* {i}\<times>{v2 j}) - a,, (b +* {i}\<times>{v1 j})) ----> k" *)
shows "(%j. (p,, (b + (i,v2 j)) - (p,, (b + (i, v1 j))))) ----> P"
proof -
  (*Proof stub: weak dominance yields
  \<forall>j . v1*[a(b2) - a(b1)] \<le> p(b2)-p(b1) \<le> v2*[a(b2) - a(b1)] 
  Sandwiched btw two sequences both converging to v*k...*)
  let ?D="Domain" let ?I="{i}" 
  let ?b2="%j. (b +* (?I \<times> {v2 j}))"
  let ?b1="%j. (b +* (?I \<times> {v1 j}))"
  let ?e="%j. (a,, (?b2 j) - (a,, (?b1 j)))"
  let ?f="%j. (v1 j)*((a,, (?b2 j)) - (a,, (?b1 j)))"
  let ?g="%j. p,, (?b2 j) - (p,, (?b1 j))"
  let ?h="%j. (v2 j)*((a,, ?b2 j) - (a,, ?b1 j))"
  (*+ and * for functions are defined in ~~/src/HOL/Library/Function_Algebras.thy*)
  have "v1 ----> v & ?e ----> k & ?f=(%j. ((v1 j) * (?e j)))" 
  using assms by fastforce then have 
  10: "?f ----> v * k" by (metis (mono_tags) tendsto_mult)
  have "?e ----> k & ?h=(%j. v2 j * ?e j) & v2 ----> v" using assms by fast hence 
  11: "?h ----> v * k" by (metis (mono_tags) tendsto_mult)
  {
    fix j let ?V1="v1 j" let ?V2="v2 j" 
    let ?Z1="?I \<times> {?V1}" let ?Z2="?I \<times> {?V2}"
    (*let ?B1="?b1 j" let ?B2="?b2 j"*)
    let ?B1="b +* ?Z1" let ?B2="b +* ?Z2" have 
    0: "?D ?Z1 \<subseteq> ?D b & ?D ?Z2 \<subseteq> ?D b" using assms by blast 
    hence 
    1: "?D ?B1 = ?D b" using assms by (metis paste_Domain sup_absorb1) 
    have 
    2: "?D ?B2 = ?D b" using 0 assms by (metis paste_Domain sup_absorb1) 
    (* also have "b \<in> (?D a) & b \<in> ?D p" using assms by blast *)
    have "?B1 \<in> ?D a" using assms cartesian_def by force
    moreover have "?B1 \<in> ?D p" using assms cartesian_def by force
    moreover have "?B2 \<in> ?D a" using assms cartesian_def by force
    moreover have "?B2 \<in> ?D p" using assms cartesian_def by force
    ultimately have 
    "?B1 \<in> ?D a & ?B2 \<in> ?D a & ?B1 \<in> ?D p & ?B2 \<in> ?D p"
    by blast
    hence
    3: "i \<in> ?D ?B1 & i \<in> ?D ?B2 & {?B1, ?B2} \<subseteq> ?D a \<inter> (?D p)" using 1 2 assms by blast
    have "?D ?Z1= ?D ?Z2" by force hence 
    4: "?B1 +* ?Z2=?B2 & ?B2 +* ?Z1=?B1" using ll53 ll56 by (metis subset_refl)
    hence "{?B1, ?B1 +* ?Z2} \<subseteq> ?D a \<inter> (?D p) & i \<in> ?D ?B1" using 3 by presburger
    hence "?V2*(a,, ?B1)-(p,, ?B1) <= ?V2*(a,, (?B1 +* ?Z2))-(p,, (?B1 +* ?Z2))" 
    using assms dom4_def by auto hence 
    "p,, ?B2-(p,, ?B1) \<le> ?V2*(a,, ?B2)-?V2*(a,, ?B1)" using 4 by force hence 
    5: "p,, ?B2 - (p,, ?B1) \<le> ?V2*((a,, ?B2) - (a,, ?B1))" using ll57 by simp
    have "{?B2, ?B2 +* ?Z1} \<subseteq> ?D a \<inter> (?D p) & i \<in> ?D ?B2" using 3 4 by auto hence 
    "?V1*(a,, ?B2) - (p,, ?B2) <= ?V1*(a,, (?B2 +* ?Z1)) - (p,, (?B2 +* ?Z1))"
    using assms dom4_def by auto hence 
    "p,, ?B2 - (p,, ?B1) \<ge> ?V1* (a,, ?B2) - (?V1* (a,, ?B1))" using 4 by force
    hence "p,, ?B2 - (p,, ?B1) \<ge> ?V1 * ((a,, ?B2) - (a,, ?B1))" using ll57 by simp
    hence "v1 j * ((a,, ?b2 j) - (a,, ?b1 j)) \<le> p,, (?b2 j) - (p,, ?b1 j) &
    p,, (?b2 j) - (p,, ?b1 j) \<le> v2 j*((a,, ?b2 j) - (a,, ?b1 j))" using 5 by fast
  }
  hence "\<forall>j. (?f j \<le> ?g j & ?g j \<le> ?h j)" by fast hence 
  "eventually (\<lambda>n. ?f n \<le> ?g n) sequentially & 
  eventually (\<lambda>n. ?g n \<le> ?h n) sequentially" by fastforce hence "?g ----> v*k" 
  using assms real_tendsto_sandwich 10 11 by fast thus ?thesis by force
qed
*)

definition weakefficient where "weakefficient a i b v a1 a2= 
(\<exists> v1 v2.( (v1 ----> v) & (v2 ----> v) &
((%j. (a``{b+*({i}\<times>{v1 j})}))=(%j. {a1})) & 
((%j. (a``{b+*({i}\<times>{v2 j})}))=(%j. {a2}))))"

lemma ll22: assumes 
"weakefficient a i b v a1 a2" 
"b \<in> Domain a" 
"cartesian (Domain a) b i"
"i \<in> Domain b" 
"runiq p"  
"Domain a \<subseteq> Domain p"
"runiq (quotient p (quotientbid i a) Id)"
"cartesian (Domain p) b i" 
"dom4 i a p"
shows 
"reducedprice p i a ,, (Domain b, b outside {i}, a2) = v * (a2 - a1) + 
reducedprice p i a ,, (Domain b, b outside {i}, a1)"
(*MC: In the canonical (Maskin's paper) case, v=max (b outside {i}), i=argmax b, 
a=delta (j,i), a1=0 and a2=1 *)
proof -
  let ?k="a2-a1" let ?d=Domain let ?I="?d b" let ?bb="b outside {i}" let ?u=runiq
  let ?q=quotient let ?p=projector let ?b="reducedbid i a" let ?B="quotientbid i a"
  let ?P="((?p (?b^-1)) O (?q p ?B Id) O ((?p Id)^-1))"
  obtain v1 where 
  21: "(v1 ----> v) & ((%j. (a``{b+*({i}\<times>{v1 j})}))=(%j. {a1}))
  " using assms weakefficient_def by metis 
  obtain v2 where 
  22: "(v2 ----> v) & ((%j. (a``{b+*({i}\<times>{v2 j})}))=(%j. {a2}))
  " using weakefficient_def assms by metis
  let ?b2="%j. b +* {i} \<times> {v2 j}"
  let ?b1="%j. b +* {i} \<times> {v1 j}"
  { 
    fix j have "a``{?b1 j}={a1} & a``{?b2 j}={a2}" using 21 22 by metis
    hence "a,,?b1 j=a1 & a,,?b2 j=a2" using eval_rel_def by auto
  }
  then have 
  20: "((%j. a,,(?b1 j))=(%j. a1)) & 
  ((%j. a,,(?b2 j))=(%j. a2))" by presburger
  (*
  obtain v1 v2 where 
  0: "(v1 ----> v) & (v2 ----> v) &
  (%j . (a ,, (b +* {i}\<times>{v1 j}))) = (%j . a1) &
  (%j . (a ,, (b +* {i}\<times>{v2 j}))) = (%j . a2)"
  using assms weakefficient_def by metis
  let ?b2="%j. b +* {i} \<times> {v2 j}"
  let ?b1="%j. b +* {i} \<times> {v1 j}" 
  *)
  have 
  4: "\<forall>j. (a,,?b1 j=a1 & a,,?b2 j=a2)" using 20 by metis
  have 
  3: "b \<in> ?d a & cartesian (Domain a) b i & i \<in> ?d b & ?u p & ?d a \<subseteq> ?d p
  & ?u (?q p ?B Id)" using assms by blast
  have "\<forall>j.(a,,(?b2 j)-(a,,(?b1 j))=?k)" using 4 by fast
  have "((%j. (a,, (?b2 j) - a,, (?b1 j)))) ----> ?k"
  using tendsto_const 4 by auto
  also have "cartesian (Domain p) b i & dom4 i a p" 
  (*  "i \<in> ?d b" "v1 ----> v" "v2 ----> v" "b \<in> ?d a \<inter> (?d p)"*)
  using assms by fast
  ultimately have 
  1: "(%j. (p,, (?b2 j) - (p,, (?b1 j)))) ----> v*?k"
  using 3 ll06 assms 21 22 by blast
  {
    fix j 
    have "?d ({i} \<times> {v1 j})={i} & ?d ({i} \<times> {v2 j})={i}" by force then have 
    "(?b1 j) outside {i}=?bb & (?b2 j) outside {i}=?bb 
    & ?d (?b1 j)=?I \<union> {i} & ?d (?b2 j)=?I \<union> {i}" 
    using ll19 Un_empty_right Un_insert_right paste_Domain by metis
    then moreover have "?d (?b1 j)=?I & ?I = ?d (?b2 j)" using 3 by blast
    then moreover have "?b1 j \<in> ?d a & ?b2 j \<in> ?d a" using 3 cartesian_def by metis
    ultimately have 
    10: "(?b1 j) outside {i}=?bb & (?b2 j) outside {i}=?bb 
    & ?d (?b1 j)=?I & ?d (?b2 j)=?I & ?b1 j \<in> ?d a & ?b2 j \<in> ?d a" by presburger
  (*  have "?d ({i} \<times> {v1 j})={i}" by force then have 
    21: "(?b1 j) outside {i}=?bb" using ll19 by (metis Un_empty_right Un_insert_right)
    have "?d (?b1 j) = ?d b \<union> ?d ({i} \<times> {v1 j})" using paste_Domain by metis
    also have "... = ?d b \<union> {i}" by force also have "... = ?d b" using 3 by fast
    ultimately have 
    11: "?d (?b1 j)=?I & ?b1 j \<in> ?d a" using 3 cartesian_def by metis
  *)
    have "p,,(?b1 j)=?P,,(?b,,(?b1 j))" using ll08 3 10 by blast
    also have "... = ?P,,(?d (?b1 j),?b1 j outside {i},(a,,?b1 j))" 
    using 10 ll20 by presburger
    also have "... = ?P,,(?I,?bb,a,,(?b1 j))" using 10 by presburger
    also have "... = ?P,,(?I,?bb,a1)" using 4 by presburger
    ultimately have 
    11: "p,,(?b1 j)=?P,,(?I,?bb,a1)" by simp
    have "p,,(?b2 j)=?P,,(?b,,(?b2 j))" using ll08 3 10 by blast
    also have "... = ?P,,(?d (?b2 j),?b2 j outside {i},(a,,?b2 j))" 
    using 10 ll20 by presburger
    also have "... = ?P,,(?I,?bb,a,,(?b2 j))" using 10 by presburger
    also have "... = ?P,,(?I,?bb,a2)" using 4 by presburger
    ultimately have "p,,(?b2 j)=?P,,(?I,?bb,a2)" by simp
    then have
    "p,,(?b2 j) - (p,, (?b1 j))=?P,,(?I,?bb,a2) - (?P,,(?I,?bb,a1))" 
    using 11 by presburger
  }
  hence "(%j. (?P,,(?I,?bb,a2) - ?P,,(?I,?bb,a1))) ----> v*?k" using 1 by presburger
  hence "?P,,(?I,?bb,a2) - (?P,,(?I,?bb,a1))= v*?k" by (metis LIMSEQ_const_iff)
  (* hence "?P,,(?I,?bb,a2) = v*?k + (?P,,(?I,?bb,a1))" by linarith*)
  thus ?thesis using reducedprice_def by fastforce
qed

corollary ll24: assumes 
"weakefficient a i b v a1 a2" 
"i \<in> Domain b" "b \<in> Domain a" "cartesian (Domain a) b i" 
"cartesian (Domain p) b i" "runiq p"  
"Domain a \<subseteq> Domain p" "dom4 i a p" "functional (Domain a)"
shows
"reducedprice p i a ,, (Domain b, b outside {i}, a2) = 
v * (a2 - a1) + reducedprice p i a ,, (Domain b, b outside {i}, a1)"
proof -
  have "weakdom i a p" using ll23 assms by fast
  hence "runiq (quotient p (part2rel (kernel (reducedbid i a))) Id)" 
  using assms ll21 by auto
  hence "runiq (quotient p (quotientbid i a) Id)" using quotientbid_def by simp
  thus ?thesis using ll22 assms by auto
qed

lemma ll35: assumes "runiq F" "f \<subseteq> F" "weakefficient f i b v a1 a2" 
shows "weakefficient F i b v a1 a2" using weakefficient_def 
proof -
  let ?w=weakefficient let ?t=trivial let ?I="{i}" obtain v1 where 
  1: "(v1 ----> v) & ((%j. (f``{b+*({i}\<times>{v1 j})}))=(%j. {a1}))
  " using assms weakefficient_def by metis obtain v2 where 
  2: "(v2 ----> v) & ((%j. (f``{b+*({i}\<times>{v2 j})}))=(%j. {a2}))
  " using weakefficient_def assms by metis
  let ?b1="%j. b+*(?I \<times> {v1 j})" let ?b2="%j. b+*(?I \<times> {v2 j})"
  {
    fix j have "f``{?b1 j} \<subseteq> F``{?b1 j} & f``{?b2 j} \<subseteq> F``{?b2 j}" 
    using assms by blast  moreover have "?t (F``{?b1 j}) & ?t (F``{?b2 j})" 
    using assms runiq_def trivial_singleton by fast  ultimately have 
    "f``{?b1 j}=F``{?b1 j} & f``{?b2 j}=F``{?b2 j}" using 1 2 ll11 by metis
    then have "F``{?b1 j}={a1} & F``{?b2 j}={a2}" using 1 2 by metis
  }
  hence "((%j. (F``{b+*({i}\<times>{v1 j})}))=(%j. {a1})) & 
  ((%j. (F``{b+*({i}\<times>{v2 j})}))=(%j. {a2}))" by presburger
  thus ?thesis using weakefficient_def 1 2 by force
qed 

corollary ll31: (*MC: MASKIN's theorem 2 as a corollary of ll24 and ll08 *)
(*MC: In the canonical (Maskin's paper) case, i=argmax b, 
a=delta (j,i), a1=0 and a2=1; this particular case of course happens to satisfy
weakefficient request below upon setting v=max (b outside {i}), and expresses 
the property that "the high bidder must win" (quoting Maskin's paper).
dom4 is weak dominance *)
assumes
"weakefficient a i b v a1 a2" 
"i \<in> Domain b" "b \<in> Domain a" "cartesian (Domain a) b i" 
"cartesian (Domain p) b i" "runiq p"  
"Domain a \<subseteq> Domain p" "dom4 i a p" "functional (Domain a)"
shows
"((a,,b=a1) \<longrightarrow> (p,,b=reducedprice p i a,,(Domain b, b outside {i}, a1))) & 
((a,,b=a2) \<longrightarrow> (p,,b = v*(a2-a1) + 
(reducedprice p i a ,, (Domain b, b outside {i}, a1))))"
proof -
  let ?P="reducedprice p i a" let ?b="reducedbid i a" let ?d=Domain 
  let ?bb="b outside {i}" let ?I="?d b"
  have "weakdom i a p" using ll23 assms by fast
  hence "runiq (quotient p (part2rel (kernel (reducedbid i a))) Id)" 
  using assms ll21 by auto
  hence "runiq (quotient p (quotientbid i a) Id)" using quotientbid_def by simp
  hence 
  0: "p,,b=?P,,(?b,,b)" using assms ll08 by (metis reducedprice_def)
  also have "... = ?P,,(?I, ?bb, a,,b)" using ll20 assms by auto
  ultimately have "(a,,b=a1) \<longrightarrow> (p,,b=?P,,(?I, ?bb, a1))" by presburger
  have "?P,,(?I, ?bb, a2)=v*(a2 - a1) + ?P,,(?I,?bb, a1)" using assms ll24 by blast
  then moreover have "(a,,b=a2) \<longrightarrow> (p,,b=v*(a2 - a1) + ?P,,(?I,?bb, a1))" 
  using 0 by (metis (full_types) `reducedprice p i a ,, (reducedbid i a ,, b) = reducedprice p i a ,, (Domain b, b outside {i}, a ,, b)`)
  ultimately show ?thesis by (metis (hide_lams, no_types) "0" `reducedprice p i a ,, (reducedbid i a ,, b) = reducedprice p i a ,, (Domain b, b outside {i}, a ,, b)`)
qed

definition effic 
::"allocation => allocation => (bid => (participant \<times> allocation) set) => bool"
(*MC: needed for reasoning *)
where
"effic a1 a2 A=(\<forall> b::bid. b \<noteq> {} \<longrightarrow>
(Range(A b)\<subseteq>{a1,a2} & b``((A b)^-1``{a2})={Sup(Range b)}))"

lemma ll29: fixes M::real shows 
"EX p1 p2. p1 ----> M & p2 ----> M & (\<forall>j. p1 j < M & p2 j > M)"
using assms
proof -
  let ?eps="%n. inverse(real(Suc n))" let ?e1="(%n. M+-?eps n)" let ?e2="(%n. M+?eps n)" 
  have "?e2 ----> M" using LIMSEQ_inverse_real_of_nat_add by force
  moreover have "?e1 ----> M" using LIMSEQ_inverse_real_of_nat_add_minus by fast
  ultimately show ?thesis by force
qed

lemma ll30: fixes A::"bid => ((participant \<times> allocation) set)" 
fixes a1::allocation fixes b::bid 
fixes i v a2 fixes P::price
assumes "a1 \<noteq> a2"
"\<forall>y.(Domain(A (b+*({i}\<times>{y}))) = Domain b & 
(* (y > (Sup (Range (b outside {i}))) \<longrightarrow> *)
runiq (A (b +* ({i}\<times>{y}))))
(* ) *)
"
"effic a1 a2 A" "i \<in> Domain b" "v=Sup(Range(b outside {i}))"
"Range (b outside {i}) \<noteq> {}" 
"(\<forall> y\<in>(Range (b outside {i})). y \<le> P)"
shows "weakefficient (graph {b +* {i} \<times> {y}|y. True} (%b. ((A b),,i))) i b v a1 a2"
proof -
  let ?af="%b. (A b,,i)" let ?G=Graph let ?a="?G ?af" let ?I="{i}" let ?u=runiq
  let ?bb="b outside ?I" let ?r=Range let ?M="Sup (?r ?bb)" let ?d=Domain 
  let ?B="{b +* ?I \<times> {y}|y. True}" let ?GG="graph ?B ?af"
  let ?GGG="{(x, ?af x)|x. x\<in>?B}"
  have
  0: "?r ?bb \<noteq> {} & (\<forall> y\<in>(?r ?bb). y \<le> P)" using assms by blast
  obtain v1 v2 where 
  1: "v1 ----> ?M & (\<forall> j.(v1 j < ?M)) & v2 ----> ?M & (\<forall> j.(v2 j > ?M))" using ll29 by blast
  {
    fix j 
    let ?b1="b+*(?I \<times> {v1 j})" let ?b2="b+*(?I \<times> {v2 j})" have 
    20: "?u (A ?b1) & ?u (A ?b2)" using assms 1 by blast have
    "?b1 \<in> ?B & ?b2 \<in> ?B" by blast then have 
    22: "?GG,,?b1=?af ?b1 & ?GG,,?b2=?af ?b2" using ll33 by smt  
    have "?d ?b1=?d b \<union> (?d (?I \<times> {v1 j}))" using paste_Domain by metis
    also have "... = ?d b" using assms by blast
    also have "... = ?d b \<union> (?d (?I \<times> {v2 j}))" using assms by blast
    also have "... = ?d ?b2" using paste_Domain by metis
    ultimately have 
    4: "?d (A ?b1)=?d ?b1 & ?d (A ?b2) \<subseteq> ?d ?b2" using assms by auto
    have "{i} \<subseteq> ?d (?I \<times> {v1 j})" by blast also have " ... \<subseteq> ?d ?b1" 
    using paste_def by blast ultimately have 
    11: "i \<in> ?d ?b1" by fast
    have "?d (?I \<times> {v2 j})=?I" by force then
    have "?b2``(?I-{})= (?I \<times> {v2 j})``(?I-{})" using ll25 by metis
    also have "... = {v2 j}" by fast ultimately have 
    3: "?b2``?I={v2 j} & ?b2 \<noteq>{}" by auto have 
    8: "v1 j < ?M & v2 j > ?M" using 1 by fast then have 
    2: "max (v2 j) ?M=v2 j & max (v1 j) ?M=?M" by linarith 
    have "?r ?b2 = ?r ?bb \<union> (?r (?I \<times> {v2 j})) " using paste_def by auto
    also have "... = ?r ?bb \<union> {v2 j}" by simp 
    also have "... = insert (v2 j) (?r ?bb)" by auto
    ultimately have "Sup (?r ?b2)=max (v2 j) ?M" using 0 by (metis (lifting) cSup_insert sup_real_def)
    also have "... = v2 j" using 2 by fastforce
    ultimately have "?b2``?I={Sup (?r ?b2)}" using 3 by presburger
    then moreover have "?b2^-1``{Sup (?r ?b2)} \<supseteq> ?I" by blast
    moreover have 
    5: "{Sup(?r ?b2)} = ?b2``((A ?b2)^-1``{a2})" using assms effic_def 3 by smt
    moreover have 
    12: "v2 j \<notin> ?r ?bb" using 8 2 by 
    (metis Un_commute Un_empty_right `Range (b +* {i} \<times> {v2 j}) = 
  Range (b outside {i}) \<union> {v2 j}` `Sup (Range (b +* {i} \<times> {v2 j})) = max (v2 j) (Sup (Range (b outside {i})))` insert_absorb insert_def less_irrefl)
    moreover have "?d (?I \<times> {v2 j})=?I" by simp then
    moreover have "?b2^-1``{v2 j} = ?bb^-1``{v2 j} \<union> (?I \<times> {v2 j})^-1``{v2 j}" using paste_def by auto
    moreover have "... = ?I" using 12 by fast
    ultimately have 
    6: "?b2^-1``{Sup(?r ?b2)} = ?I" using 3 by metis
    have "(A ?b2)^-1``{a2} \<subseteq> ?b2^-1 `` (?b2``((A ?b2)^-1``{a2}))" using 4 by fast
    also have "... = ?b2^-1``{Sup (?r ?b2)}" using 5 by presburger
    ultimately have "(A ?b2)^-1``{a2} \<subseteq> ?I & (A ?b2)^-1``{a2} \<noteq> {}" 
    using 5 6 by fast
    hence "(A ?b2)^-1``{a2}=?I" by blast
    hence "{a2} \<subseteq> (A ?b2)``?I" by fast
    (* MC: bring this out of this cycle *) 
    hence "(A ?b2)``?I = {a2}" using 20 
    by (metis `(A (b +* {i} \<times> {v2 j}))\<inverse> \`\` {a2} = {i}` ll71 subset_antisym)
    (*MC: "{a2}=(A ?b2)``?I" makes this deduction much harder: = is not effectively commutative :) *)
    moreover have "(A ?b2)``?I={?af ?b2}" 
    by (metis Image_runiq_eq_eval assms(2) assms(4))  
    moreover have "... = ?GGG``{?b2}" using ll88 by blast ultimately have 
    15: "?GG``{?b2}={a2}" using graph_def by metis
  (*
    then have "a2=?af ?b2" by fastforce 
    also have "... = ?GG,,?b2" using 22 by presburger ultimately have 
    15: "?GG,,?b2=a2" by presburger
    then have "A ?b2,,i=a2" by fastforce 
    also have "?a,,?b2=?af ?b2" using ll28 by metis ultimately have 
    15: "?a,,?b2 = a2" by fastforce
  *)
    have "?r ?b1 = ?r ?bb \<union> (?r (?I \<times> {v1 j})) " using paste_def by auto
    also have "... = ?r ?bb \<union> {v1 j}" by simp 
    also have "... = insert (v1 j) (?r ?bb)" by auto
    ultimately have "Sup (?r ?b1)=max (v1 j) ?M" using 0 by (metis (lifting) cSup_insert sup_real_def) 
    then have "{v1 j} \<noteq> {Sup (?r ?b1)}" using 8 by force
    also have "?d (?I \<times> {v1 j})=?I" by blast then
    moreover have "?b1``(?I-{})=(?I \<times> {v1 j})``(?I-{})" using ll25 by metis
    ultimately have "\<not> {i} \<subseteq> ?b1^-1``{Sup (?r ?b1)}" by force
    moreover have 
    14: "?b1 \<noteq> {}" using paste_def by auto then 
    moreover have "?b1^-1``{Sup (?r ?b1)} = ?b1^-1``(?b1``((A ?b1)^-1``{a2}))" 
    using assms effic_def paste_def by force
    moreover have "... \<supseteq> (A ?b1)^-1``{a2}" using 4 by blast
    ultimately have "i \<notin> (A ?b1)^-1``{a2}" by fast
    moreover have 
    13: "i \<in> ?d (A ?b1)" using 4 assms by metis
    ultimately have "A ?b1``?I \<subseteq> ?r (A ?b1) - {a2}" by fast
    moreover have "... \<subseteq> {a1, a2} - {a2}" using assms effic_def 14 
    by blast
    also have "...={a1}" using assms(1) by fast
    also have "i \<in> ?d (A ?b1)" using 4 assms 11 by blast
    ultimately have "A ?b1``?I = {a1}" using 4 assms by blast
    moreover have "(A ?b1)``?I={?af ?b1}" 
    by (metis Image_runiq_eq_eval assms(2) assms(4))  
    moreover have "... = ?GGG``{?b1}" using ll88 by blast ultimately have 
    "?GG``{?b1}={a1} & ?GG``{?b2}={a2}" using 15 graph_def by metis
  (*
    then have "a1=?af ?b1" by fastforce
    also have "... = ?GG,,?b1" using 22 by presburger
    ultimately have "?GG,,?b1=a1 & ?GG,,?b2=a2" using 15 by presburger
    then have "?a,,?b1=a1" using ll28 by (metis RelationOperators.eval_rel.simps the_elem_eq)
    then have "?a,,?b1=a1 & ?a,,?b2=a2" using 15 by blast
  *)
  }
  hence "(%j. (?GG``{b+*({i}\<times>{v1 j})}))=(%j. {a1})
  & (%j. (?GG``{b+*({i}\<times>{v2 j})}))=(%j. {a2})" by presburger
  (* hence "(%j. (?GG,,(b+*({i}\<times>{v1 j}))))=(%j. a1)
  & (%j. (?GG,,(b+*({i}\<times>{v2 j}))))=(%j. a2)" by presburger
  *)
  thus ?thesis using 1 weakefficient_def assms by fastforce
qed

definition converter where "converter F i=graph runiqs (%b. (F b),,i)"

corollary (* of ll30 and ll31 *)
(*MC: A step towards a more familiar statement of Maskin2 theorem.
A further improvement could be to get rid of converter, or
to express it in a more comprehensible way.
That object is needed because of the constant duality between 
set-theoretical functions (aka graphs of runiq relations)
and type-theoretical ones (first-class \<lambda> abstractions)*)
assumes 
"effic 0 1 A"
"i \<in> Domain b"
"runiq b"
"dom4 i (converter A i) (converter P i)"
"\<forall> y\<in>(Range (b outside {i})). y \<le> M"
"\<not> (trivial b)"
"f = (%i. reducedprice (converter P i) i (converter A i))"
"\<forall>y.(Domain(A (b+*({i}\<times>{y}))) = Domain b & runiq (A (b +* ({i}\<times>{y}))))"
shows "
((A b,,i=0)\<longrightarrow> (P b,,i=f i,,(Domain b,b outside {i},0))) &
((A b,,i=1)\<longrightarrow> (P b,,i=f i,,(Domain b,b outside {i},0) + Sup(Range(b outside {i}))))"
proof -
  let ?w=weakefficient let ?d=Domain let ?r=Range let ?z="0::nat" let ?o="1::nat"
  let ?u=runiq let ?g=graph let ?C=cartesian let ?t=trivial let ?U=runiqs
  let ?I="{i}" let ?B="{b +* ?I \<times> {y}|y. True}" let ?af="%b. A b,,i" 
  let ?bb="b outside ?I" let ?c=converter let ?a="?c A i" let ?p="?c P i"
  let ?pf="%b. P b,,i" let ?GG="graph ?B ?af" let ?v="Sup(?r(b outside {i}))"
  have "?d (b || ?I) = (?d b) \<inter> ?I" using ll41 by metis
  then have "?d (b||?I) \<subseteq> ?I & ?d ?bb = (?d b) - ?I" using ll42 by (metis Int_lower2)
  then have "?d ?bb \<inter> (?d (b || ?I))={}" by blast
  then have "?bb \<inter> (b||?I)={}" by fast
  hence "?bb=?bb \<union> (b||?I) - (b||?I)" by blast
  also have "... = b - (b||?I)" using outside_union_restrict by blast
  ultimately have "?bb=b - (b|| ?I)" by presburger
  moreover have "?t (b``?I)" using assms by (metis runiq_alt) then
  moreover have "?t (b||?I)" 
  using ll40 trivial_singleton restrict_to_singleton by metis 
  ultimately have "?bb \<noteq> {}" using ll26 assms by auto hence 
  2: "?r ?bb \<noteq> {}" by fast
  have "b \<in> {f. ?u f}" using assms by force also have "...=runiqs" using runiqs_def
  by blast also have  "...=?d ?a" using converter_def ll37 by metis
  ultimately have
  1: "?d ?a=runiqs & b \<in> ?d ?a & ?d ?p=runiqs" using converter_def ll37 by metis
  have "?a=graph runiqs ?af" using converter_def by fast
  have "\<forall>y. ?u (?I \<times> {y})" using runiq_singleton_rel by fastforce then
  have "\<forall>y. ?u (b +* (?I \<times> {y}))" using runiq_paste2 assms by metis
  then have "runiqs = ?B \<union> runiqs" using runiqs_def by blast
  moreover have "?g ?B ?af \<subseteq> ?g (?B \<union> runiqs) ?af" using ll34 by blast
  ultimately have "?GG \<subseteq> ?a" using converter_def by force
  moreover have "?u ?a" using ll37 converter_def by metis
  moreover have "?r ?bb \<noteq> {}" using 2 by auto
  then moreover have "?w ?GG i b ?v ?z ?o" using ll30 assms by auto
  ultimately have "?w ?a i b ?v ?z ?o" using ll35 by fastforce
  moreover have "i \<in> ?d b" using assms by force
  moreover have "b \<in> ?d ?a" using 1 by fastforce
  moreover have "?C (?d ?a) b i" using ll39 converter_def assms by metis
  moreover have "?C (?d ?p) b i" using ll39 converter_def assms by metis
  moreover have "?u ?p" using ll37 converter_def by metis
  moreover have "?d ?a \<subseteq> ?d ?p" using 1 by auto
  moreover have "dom4 i ?a ?p" using assms by fast
  moreover have "functional (?d ?a)" using 1 runiqs_def functional_def by fast
  ultimately have
  "
  ((?a,,b=?z) \<longrightarrow> (?p,,b=reducedprice ?p i ?a,,(?d b, b outside {i}, ?z)))
  &
  ((?a,,b=?o) \<longrightarrow> (?p,,b = ?v*(?o-?z) + 
  (reducedprice ?p i ?a ,, (Domain b, b outside {i}, ?z))))
  " 
  using ll31 assms by fastforce
  moreover have "?v*(?o-?z) = ?v" by fastforce
  moreover have "?a``{b} = ?g ?U ?af``{b}" using converter_def by fast
  moreover have "... = {(x, ?af x)|x. x\<in>?U}``{b}" using graph_def by force
  moreover have "...={?af b}" using assms runiqs_def 1 ll88 by blast
  moreover have "...={A b,,i}" by auto
  moreover have "?p``{b} = ?g ?U ?pf``{b}" using converter_def by fast
  moreover have "... = {(x, ?pf x)|x. x\<in>?U}``{b}" using graph_def by metis
  moreover have "...={?pf b}" using assms runiqs_def 1 ll88 by blast
  moreover have "...={P b,,i}" by auto
  moreover have "reducedprice ?p i ?a=f i" using assms by fast
  ultimately show ?thesis by force
qed


(* Old/experimental stuff

definition weakefficientOld where "weakefficientOld a i = 
(\<forall> b::bid . \<exists> v v1 v2 a1 a2. 
(v1 ----> v) &
(v2 ----> v) &
(%j . (a ,, (b +* {(i, v1 j)}))) = (%j . a1) &
(%j . (a ,, (b +* {(i, v2 j)}))) = (%j . a2) &
(a1 \<noteq> a2)
)" 

lemma assumes "dom2 i a p" shows "weakdom i a p" 
using dom2_def weakdom_def assms by smt

lemma assumes "dom4 i (a || runiqs) p" 
shows "dom2 i (a || runiqs) p" 
proof -
  let ?D="Domain" let ?F="runiqs" let ?aa="a || ?F"
  let ?f="% Y::(price set). % y::allocation. (the_elem Y * y)"
  let ?P="%f. (\<forall> b::bid. \<forall> Y::(price set). ({b, b+*({i}\<times>Y)} \<subseteq> (?D ?aa \<inter> (?D p)) & i \<in> ?D b
  \<longrightarrow>
  (f Y (?aa,, b))-(p,, b) \<le> (f Y (?aa,, (b+* ({i}\<times>Y)))) - (p,, (b+* ({i}\<times>Y)))))"
  have "\<forall> b::bid. \<forall> Y::(price set). (
  ({b, b+*({i}\<times>Y)} \<subseteq> (?D ?aa \<inter> (?D p)) & i \<in> ?D b)
  \<longrightarrow>
  (?f Y (?aa,, b))-(p,, b) \<le> (?f Y (?aa,, (b+* ({i}\<times>Y)))) - (p,, (b+* ({i}\<times>Y))))"
  proof 
    fix b::bid   
    show "\<forall> Y::(price set). (
    ({b, b+*({i}\<times>Y)} \<subseteq> (?D ?aa \<inter> (?D p)) & i \<in> ?D b)
    \<longrightarrow>
    (?f Y (?aa,, b))-(p,, b) \<le> (?f Y (?aa,, (b+* ({i}\<times>Y)))) - (p,, (b+* ({i}\<times>Y))))"
    proof 
      fix Y::"price set" let ?Z="{i}\<times>Y" let ?bb="b +* ?Z" let ?y="the_elem Y"
      show 
  "{b, ?bb} \<subseteq> ?D ?aa \<inter> ?D p & i \<in> ?D b \<longrightarrow>
  (?f Y (?aa,, b))-(p,, b) \<le> (?f Y (?aa,, ?bb)) - (p,, ?bb)"
      proof 
        assume 4: "{b, ?bb} \<subseteq> ?D ?aa \<inter> ?D p & i \<in> ?D b"
        hence 0: "{b, ?bb} \<subseteq> ?D ?aa \<inter> ?D p & ?D ?Z \<subseteq> ?D b" by fast
        hence "?bb \<in> ?D ?aa" by simp hence "?bb \<in> runiqs" using restrict_def by auto
        hence 3: "runiq ?bb" using runiqs_def restrict_def by blast
        {
          assume 8: "Y \<noteq> {}" then
          have 9: "?D b = ?D ?bb" using 0 by (metis Un_commute paste_Domain subset_Un_eq)
          have "?D ?Z \<inter> {i}={i}" using 8 by fast then
          have "?bb `` {i} = (?Z``{i})" using ll50 by metis
          also have "... = Y" by fast
          ultimately have "Y=?bb `` {i} & trivial Y" using 3 l32 by metis
          hence "trivial Y & Y \<noteq> {}" using 9 4 by auto
          hence 1: "Y={?y}" using runiq_def trivial_def by blast
          hence "{b, b+* ({i}\<times>{?y})} \<subseteq> (?D ?aa \<inter> (?D p)) & i \<in> ?D b" using 0 by auto
          hence "(?f Y (?aa,, b))-(p,, b) \<le> (?f Y (?aa,, ?bb)) - (p,, ?bb)" 
          using 1 assms dom4_def by metis
        }
        also have "Y ={} --> (?f Y (?aa,, b))-(p,, b) \<le> (?f Y (?aa,, ?bb)) - (p,, ?bb)" 
  using l38 by 
  (metis (mono_tags) Domain_empty Sigma_empty2 order_refl paste_outside_restrict restrict_empty)
        ultimately show "(?f Y (?aa,, b))-(p,, b) \<le> (?f Y (?aa,, ?bb)) - (p,, ?bb)"
        by fast
      qed    
    qed
  qed
  have "\<forall> b::bid. \<forall> Y::(price set). ({b, b+*({i}\<times>Y)} \<subseteq> (Domain ?aa \<inter> (Domain p)) & i \<in> Domain b
  \<longrightarrow>
  (?f Y (?aa,, b))-(p,, b) \<le> (?f Y (?aa,, (b+* ({i}\<times>Y)))) - (p,, (b+* ({i}\<times>Y))))" sory 
  then
  have "?P ?f" by fast then
  have "EX f. (?P f)" by fastforce
  hence "dom2 i ?aa p" using dom2_def by presburger
  thus ?thesis by simp
qed

definition weakdomgen
(* ::"participant => (bid \<times> allocation) set => (bid \<times> price) set => bool" *)
where "weakdomgen P i a p = ( \<forall> b::bid . 
\<forall> Y. (P Y) \<longrightarrow>  
(EX f. f (a,, b) - (p,, b) \<le> f (a,, (b+* ({i} \<times> Y))) - (p,, (b+*({i} \<times> Y))))
(* \<forall> r::price . 
r* (a,, b)-(p,, b) \<le> r* (a,, (b+* ({i}\<times>{r}))) - p,, (b+* ({i}\<times>{r}))*)
)" 

*)

end

