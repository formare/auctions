theory RelationQuotient

imports "../MiscTools" "../RelationProperties"

begin

lemma l14b: "runiq (Graph f)"
proof -
  have "runiq {(x, f x)|x. True}" using l14 by fast thus ?thesis using Graph_def by metis
qed

corollary l15: fixes R::"('a \<times> 'b) set" shows "runiq (projector R)"
proof -
let ?f="%x . R``{x}" let ?P="%x . x\<in>Domain R" let ?F="projector R"
(* let ?P="%x. True" *)
have "?F={(x,?f x) | x::'a . ?P x}" using projector_def by blast
also have "runiq {(x,?f x) | x::'a . ?P x}" using l14 by fast
ultimately show ?thesis by fastforce
qed

corollary l17: fixes R::"('a \<times>'b ) set" fixes xx::"'a" 
assumes "xx \<in> Domain R"
shows "projector R ,, xx = R `` {xx}" 
proof -
let ?D="Domain R" let ?f="%x . (R `` {x})" let ?r="projector R"
let ?P="%xx . (xx \<in> ?D)"
(* let ?P="%x. True" *)
let ?F="{(x, ?f x) | x. ?P x}"
have "?P xx" using assms by fast
hence "?F ,, xx = ?f xx" by (rule l16)
(*MC: try0 and sledgehammer fail here for me! *)
also have "?r=?F" using projector_def by blast
ultimately show ?thesis by presburger
qed

lemma l19: fixes f P shows "Range {(x, f x)| x. P x}= {f x | x. P x}"
proof -
let ?X="{(x, f x) | x. P x}" let ?LH="Range ?X" let ?RH="{f x | x. P x}"
have "?LH \<subseteq> ?RH & ?RH \<subseteq> ?LH" by blast thus ?thesis by fastforce
qed

corollary l20: fixes R shows "Range (projector R)={R``{x}| x. x\<in>Domain R}"
proof -
let ?D="Domain R" let ?P="% x. x \<in> ?D" let ?p="projector R"
let ?f="%x . R``{x}" let ?X="{(x,?f x)|x. ?P x}" 
let ?lh="Range ?X" let ?rh="{?f x | x. ?P x}"
let ?LH="Range ?p" let ?RH="{?f x| x. x \<in> ?D}"
have "?lh=?LH & ?rh=?RH" using projector_def by fastforce
thus ?thesis using l19 by metis
qed

lemma l27: fixes r assumes "equiv (Domain r) r" 
shows "Range (projector r) = Domain r // r"
proof -
let ?R="projector r" let ?d="Domain r" let ?RH="?d // r" 
let ?f="% x . r `` {x}" let ?LH="Range ?R" let ?MH="{?f x | x. x \<in> ?d}"
have "?RH = (\<Union> x\<in>?d . {?f x})" using Equiv_Relations.quotient_def by blast
hence "?MH = ?RH" using Equiv_Relations.quotient_def by auto
also have "?LH=?MH" using l20 by metis ultimately show "?LH = ?RH" by force
qed

lemma l21: fixes x p assumes "equiv (Domain p) p" 
assumes "x \<in> Domain p"
shows
"{X. ((X \<in> Range (projector p)) & x \<in> X)} = {p `` {x}}"
proof -
let ?P="projector p" let ?D="Domain p" let ?LH="{X. X\<in> Range ?P & x \<in> X}"
let ?XX="p `` {x}" let ?RH="{?XX}" have 
1: "x \<in> ?XX" using equiv_class_self assms by metis have 
2: "?XX \<in> Range ?P" using assms l20 by blast hence "?XX \<in> ?LH" using assms 1 2 by blast hence 
5: "?RH \<subseteq> ?LH" by fast
{
  fix XX assume "XX \<in> ?LH" hence 
  3: "XX \<in> Range ?P & x\<in>XX" by fast
  have 4: "XX \<in> ?D//p & ?XX \<in> ?D//p" using 3 2 l27 assms by fast
  hence "?XX \<inter> XX \<noteq> {}" using 1 3 by fast 
  hence "?XX=XX" using quotient_disj 4 assms by metis
  hence "XX \<in> ?RH" by fast
}
thus ?thesis using 5 by blast 
qed

lemma l0:  
(* fixes x::'a fixes p::"('a \<times> 'a) set" *)
assumes "equiv (Domain p) p" "x \<in> Domain p" shows
"{X. (X \<in> Range (projector p)) & x \<in> X} = {projector p ,, x}" (is "?LH=_")
proof -
have "equiv (Domain p) p" using assms by auto moreover have "x\<in>Domain p" using assms by auto
ultimately have "?LH = {p `` {x}}" by (rule l21) then show ?thesis using assms l17 by metis
qed

lemma l1: (* fixes r x p q *) assumes "Domain r \<subseteq> \<Union> Range (projector p)" "Range r \<subseteq> \<Union> Range (projector q)"
shows "r``{x} \<subseteq> \<Union> ((quotient r p q) `` {X . X \<in> Range (projector p) & x \<in> X})"
proof -
let ?lh="r``{x}" let ?R="quotient r p q" let ?P="projector p"
let ?Q="projector q" let ?Sx="{X. X \<in> Range ?P & x \<in> X}"
let ?RH="?R `` ?Sx" let ?rh="\<Union> ?RH"
{
  fix y assume 0: "y \<in> ?lh"
  hence 1: "(x,y) \<in> r" by fast
  obtain "px" where 5: "px \<in> Range ?P & x \<in> px" using assms 0 by blast
  obtain "qy" where 6: "qy \<in> Range ?Q & y \<in> qy" using assms 0 by blast    
  have 2: "(x,y) \<in> px \<times> qy" using 5 6 by fast
  have 3: "px \<in> Range ?P" using 5 6 by fast
  have 4: "qy \<in> Range ?Q" using 5 6 by fast
  have "(px, qy) \<in> ?R" using quotient_def 1 2 3 4 by force
  hence "qy \<in> ?RH" using 1 2 3 4 by blast
  hence "y \<in> ?rh" using 2 by blast
}
thus ?thesis by fastforce
qed

lemma l3: fixes r q x p assumes "equiv (Domain p) p" 
assumes "runiq (quotient r p q)"
assumes "x \<in> Domain p"
shows 
"(quotient r p q) `` {X . X \<in> Range (projector p) & x \<in> X} 
\<subseteq> {(quotient r p q) ,, ((projector p) ,, x)}"
proof -
(* let ?F="quotient r p q" let ?P="projector p"
let ?XX="{X. X \<in> Range ?P | x \<in> X}"
have "?XX = {?P ,, x}" using l0 assms by fast
thus "?F `` ?XX \<subseteq> {?F ,, (?P ,, x)}" using l2 by (smt assms(2))*)
show ?thesis using l0 runiq_wrt_eval_rel assms by (metis (no_types))
qed

lemma l9: fixes Y P shows "snd ` {(x,y) . y\<in>Y & P} \<subseteq> Y"
(* TODO MC: shorten this proof *)
proof -
let ?R="{(x,y) . y \<in> Y & P}" let ?POH="snd ` ?R"
{
  fix y assume "y \<in> snd `?R" (* WHY CAN'T I USE ?POH here ???! *) 
  then obtain z where 1: "z \<in> ?R & y=snd z" by fastforce
  have "y \<in> Y" using 1 by fastforce
}
thus "snd ` ?R \<subseteq> Y" by force
qed

lemma l12: fixes r p q
(* MC: probably useless
   CL@MC: you can find out by putting unused_thms at the end of your theory *)
shows "Range (quotient r p q) \<subseteq> Range (projector q)"
proof -
let ?R="quotient r p q" let ?Q="projector q" let ?P="projector p"
have "?R={(x,y)|x y. y \<in> Range ?Q & x \<in> Range ?P & x \<times> y \<inter> r \<noteq> {}}" using quotient_def by blast
hence "snd ` ?R \<subseteq> (Range ?Q)" using l9 by force thus ?thesis using Range_snd by metis 
qed

lemma l13: fixes r x p q
assumes "equiv (Domain p) p" 
assumes "runiq (quotient r p q)"
assumes "Domain r \<subseteq> \<Union> Range (projector p)" 
assumes "Range r \<subseteq> \<Union> Range (projector q)"
assumes "x\<in>Domain p"  
shows "r``{x} \<subseteq> (quotient r p q) ,, ((projector p) ,, x)"
using assms l1 l3 by fast

lemma l5: "((Graph id) `` {x}) = {x}" using id_def l4 by (metis image_id)

lemma l6: "(projector (Graph id)) \<supseteq> {(x,{x}) | x . x \<in> Domain (Graph id)}"
unfolding projector_def l5 by fastforce

lemma l7: "(projector (Graph id)) = {(x,{x}) | x . x \<in> Domain (Graph id)}" and 
"Range {(x,{x})| x. x \<in> Domain (Graph id)}={{x}| x .x \<in> Domain (Graph id)}"
proof 
let ?Id="Graph id" let ?X="Domain ?Id" let ?LH="projector ?Id"
let ?RH="{(x,{x}) | x. x \<in> ?X}"
{
  fix y assume "y \<in> ?LH" then
  have "y \<in> { (x,?Id``{x}) | x . x \<in> ?X}" using projector_def by blast 
  then obtain x where 1: "y=(x,?Id``{x}) & x \<in> ?X" using projector_def by blast
  have "y \<in> ?RH" using l5 1 by fast 
}
thus "?LH \<subseteq> ?RH" by blast
thus "?LH \<supseteq> ?RH" using l6 by blast
show "Range {(x,{x}) | x . x \<in> Domain (Graph id)} 
= {{x} | x . x\<in>Domain (Graph id)}" using Range_snd Range_def by auto 
qed

lemma l10: fixes X i assumes "i \<subseteq> (Graph id)" 
assumes "X \<in> Range (projector i)" shows "trivial X"
proof -
let ?d="Domain i" let ?I="Graph id"
have "X \<in> {i``{x}| x. x \<in> ?d}" using l20 assms by metis
then obtain x where 1: "X=i``{x} & x\<in>?d" by blast
have "i``{x} \<subseteq> ?I ``{x}" using assms by fast
hence "X \<subseteq> ?I `` {x}" using 1 by simp
also have "... = id `{x}" using l4 by metis
also have "... = {x}" by auto
finally have "X \<subseteq> {x}" by fast 
thus ?thesis using trivial_def by (metis "1" Image_within_domain' subset_singletonD the_elem_eq)
qed

lemma l28: fixes r p x q assumes "projector p ,, x \<in> Domain (quotient r p q)"
assumes "runiq (quotient r p q)"
assumes "q \<subseteq> Graph id"
shows "trivial (quotient r p q ,, (projector p ,, x))"
proof -
let ?P="projector p" let ?R="quotient r p q"
let ?Y="?R ,, (?P ,, x)"
have "(?P ,, x, ?R ,, (?P ,, x)) \<in> ?R" using assms eval_runiq_rel by fast
hence "?R ,, (?P ,, x) \<in> Range ?R" by fast
hence 2: "?Y \<in> Range (projector q)" using l12 by blast
thus "trivial ?Y" using l10 2 assms by blast
qed

corollary (* l29: *) assumes
 "equiv (Domain p) p" 
 "runiq (quotient r p q)" (* l23, l24 for that *)
 "Domain r \<subseteq> \<Union> Range (projector p)" 
 "Range r \<subseteq> \<Union> Range (projector q)"
 "x\<in>Domain p"
 "runiq r"
 "x \<in> Domain r"
 "q \<subseteq> Graph id"
 "projector p ,, x \<in> Domain (quotient r p q)"
shows "r ,, x = the_elem (quotient r p q ,, (projector p ,, x))"
proof -
let ?P="projector p" let ?R="quotient r p q" let ?Y="?R ,, (?P ,, x)"
have "r `` {x} \<supseteq> {r ,, x}" using assms runiq_wrt_eval_rel Image_within_domain' by (metis subset_singletonD)
hence "{r ,, x} \<subseteq> ?Y" using l13 assms by fast
thus "r ,, x = the_elem ?Y" using l28 assms singleton_sub_trivial_uniq by fast
qed

lemma l35: shows "projector (Graph id)={(x,{x})|x. True}" (is "?LH=?RH")
using projector_def Graph_def id_def
proof -
let ?I="Graph id" let ?II="{(x,x)|x. True}" let ?D="Domain ?I"
let ?LH2="projector ?II"
term "Domain ?I"
let ?RH2="{(x, ?I `` {x})|x. x\<in>?D}"
let ?RH1="{(x,{x})|x. x\<in>?D}"
have "?LH \<supseteq> ?RH2" using assms projector_def Graph_def id_def by fast
also have "?LH \<subseteq> ?RH2" using assms projector_def Graph_def id_def by auto
ultimately have "?LH = ?RH2" by fast
also have "... = ?RH1" by (metis l5)
also have "... = ?RH" by (metis Image_within_domain' insert_not_empty l5)
ultimately show ?thesis by presburger
qed

lemma l23: assumes lc: "compatible g p q" 
assumes lr: "runiq g" 
assumes lt: "trans p"
assumes ls: "sym p"
assumes le: "equiv (Domain q) q"
shows "runiq (quotient g p q)" (is "runiq ?G")
proof -
let ?r="runiq" let ?pr="projector" let ?R="Range"
let ?P="?pr p" let ?Q="?pr q" let ?RP="?R ?P" let ?RQ="?R ?Q"
let ?GG="{(x,y)| x y. y \<in> ?RQ & x \<in> ?RP & x \<times> y \<inter> g \<noteq> {}}"
{
  fix X Y1 Y2 assume "(X, Y1) \<in> ?GG" hence 3: "X \<in> ?RP & Y1 \<in> ?RQ & X \<times> Y1 \<inter> g \<noteq> {}" by simp
  hence "X \<in> Range {(x, p `` {x})|x. x\<in> Domain p}" using projector_def by metis
  then obtain x where 
  10: "x\<in> Domain p & X = p``{x}" 
  using projector_def Range_def by blast
  obtain x1 y1 where 1: "(x1, y1) \<in> X \<times> Y1 \<inter> g" using 3 by auto  
  assume "(X, Y2) \<in> ?GG" hence 4: "Y2 \<in> ?RQ & X \<times> Y2 \<inter> g \<noteq> {}" by simp
  then obtain x2 y2 where 2: "(x2, y2) \<in> X \<times> Y2 \<inter> g" by blast
  have "x1 \<in> X & x2 \<in> X" using 1 2 by fastforce 
  hence "x1 \<in> p `` {x} & x2 \<in> p `` {x}" using 10 by auto
  hence "(x1,x) \<in> p & (x,x2) \<in> p" using ls by (metis Image_singleton_iff symD)
  hence "(x1,x2) \<in> p" using lt transD by metis
  hence "{x2} \<subseteq> p `` {x1}" by fastforce hence
  "g `` {x2} \<subseteq> g `` (p `` {x1})" by blast
  also have "... \<subseteq> q `` (g `` {x1})" using lc compatible_def by metis
  also have "... \<subseteq> q `` {g ,, x1}" using lr 1 by (metis Image_empty equals0D runiq_wrt_eval_rel subsetI subset_singletonD)
  also have "... \<subseteq> q `` {y1}" using 1 l31 lr by fast
  ultimately have "{y2} \<subseteq> q `` {y1}" using 2 l31 by blast
  hence "(y1,y2) \<in> q & y1 \<in> Y1 & y2 \<in> Y2 & Y1 \<in> (Domain q)//q
  & Y2 \<in> (Domain q)//q & equiv (Domain q) q" using 1 2 3 4 le l27 by auto
  hence "Y1=Y2" by (metis quotient_eq_iff)
}
hence "runiq ?GG" using runiq_basic quotient_def 
proof -
  have "\<And>x\<^sub>1 X_2 x. x\<^sub>1 = X_2 \<or> (x, X_2) \<notin> quotient g p q \<or> (x, x\<^sub>1) \<notin> quotient g p q" 
by (metis quotient_def `\<And>Y2 Y1 X. \<lbrakk>(X, Y1) \<in> {(x, y) |x y. y \<in> Range (projector q) \<and> x \<in> Range (projector p) \<and> x \<times> y \<inter> g \<noteq> {}}; (X, Y2) \<in> {(x, y) |x y. y \<in> Range (projector q) \<and> x \<in> Range (projector p) \<and> x \<times> y \<inter> g \<noteq> {}}\<rbrakk> \<Longrightarrow> Y1 = Y2`) (* failed *)
  thus "runiq {(x, y) |x y. y \<in> Range (projector q) \<and> x \<in> Range (projector p) \<and> x \<times> y \<inter> g \<noteq> {}}" 
using runiq_basic 
by (metis (erased, lifting) `\<And>Y2 Y1 X. \<lbrakk>(X, Y1) \<in> {(x, y) |x y. y \<in> Range (projector q) \<and> x \<in> Range (projector p) \<and> x \<times> y \<inter> g \<noteq> {}}; (X, Y2) \<in> {(x, y) |x y. y \<in> Range (projector q) \<and> x \<in> Range (projector p) \<and> x \<times> y \<inter> g \<noteq> {}}\<rbrakk> \<Longrightarrow> Y1 = Y2`)
(* by (metis (no_types)  uniq_right_comp_imp_runiq)*)
qed
thus ?thesis using quotient_def by metis
qed

lemma assumes "runiq f" assumes "compatible f p q" shows "
(\<forall> x. (f `` (p `` {x})) \<subseteq> q `` {f ,, x})" 
using assms l32 trivial_def compatible_def by 
(metis (hide_lams, no_types) Image_empty eval_rel.simps empty_subsetI subset_empty subset_singletonD)

lemma assumes "runiq f" "\<forall> x. (f `` (p `` {x}) \<subseteq> q `` {f ,, x})" shows "\<forall>x \<in> Domain f . (f `` (p `` {x}) \<subseteq> q `` (f `` {x}))"
using assms by (metis Image_runiq_eq_eval)

lemma l34: "compatible r p q = (\<forall> x\<in> Domain p .(r `` (p `` {x}) \<subseteq> q `` (r ``{x})))"
using compatible_def by fast

lemma l43: "\<Union> ((op `` R) ` X)= R ``(\<Union> X)" using Image_def by blast

lemma l44: "\<Union> Range (projector R) \<supseteq> Range R" using projector_def Image_def by blast

lemma l45: "Range (projector R) \<subseteq> Pow (Range R)" (is "?LH \<subseteq> ?RH")
proof -
have "?LH={R``{x}|x. x \<in> Domain R}" by (metis l20) 
also have "... \<subseteq> Pow (Range R)" by fast
ultimately show ?thesis by simp
qed

corollary l46: "\<Union> Range (projector R) = Range R" 
using l44 l45 by (metis Union_Pow_eq Union_mono antisym)

lemma assumes "runiq R" shows "(\<forall> x y1 y2. (x,y1) \<in> R & (x,y2)\<in>R \<longrightarrow> y1=y2)"
using assms l31 by metis

lemma l30: "runiq {(x, THE y. y\<in>R``{x})| x. x\<in>Domain R}" using assms runiq_def l14 by fast

corollary "runiq (runiqer R)" using l30 runiqer_def by metis

lemma ll47: assumes "finite R" shows "card (Domain R) \<le> card R & card (Range R) \<le> card R"
(is "card ?D \<le> card R & card ?R \<le> card R")
(* MC: Could be weakened by asking only finite (Domain R) (resp Range R) *)
proof -
have "?D = fst ` R & ?R = snd ` R" by force
thus ?thesis using card_image_le assms by metis
qed

lemma "kernel R = {R^-1``{y}| y. y\<in>Range R}"
proof -
let ?k=kernel let ?r=Range let ?f=finestpart let ?R="?r R" 
let ?RH="{R^-1 ``{y}| y. y \<in> ?r R}" 
let ?LH="(op `` (R^-1)) ` (?f ?R)"
{  
  fix y assume "y \<in> ?r R" hence "{y} \<in> ?f ?R" 
  using finestpart_def by auto hence "R^-1 `` {y} \<in> ?LH"  by blast
} 
then have 0: "?LH \<supseteq> ?RH" by blast
{
  fix Y assume "Y \<in> ?f ?R" also have "?f ?R={{y}| y. y \<in> ?R}" using ll64 by blast
  ultimately obtain y where 
  1: "Y={y} & y \<in> ?R" using finestpart_def by auto
  have "R^-1 `` Y \<in> ?RH" using 1 by blast
}
then have "?LH \<subseteq> ?RH" by blast 
also have "?LH = ?k R" using kernel_def by auto
ultimately show ?thesis using 0 by force
qed

lemma ll66: assumes "runiq f" "y1 \<in> Range f" "y2 \<in> Range f" shows 
"(f^-1 `` {y1} \<inter> f^-1 `` {y2} \<noteq> {}) = (y1=y2)"
using assms ll71 by fast

lemma ll61: assumes "refl_on X P" "x\<in>X" shows "x \<in> P``{x}" using refl_on_def assms
by (metis Image_singleton_iff)

lemma ll62: assumes "equiv (Domain p) p" "X \<in> Range (projector p)"
shows "(x,X) \<in> projector p = (x \<in> X)" (is "?LH = ?RH")
proof -
let ?p=projector let ?P="?p p" let ?d=Domain let ?r=Range 
have 0: "?P = {(x, p``{x})| x. x\<in> ?d p}" using projector_def by blast
also have "refl_on (?d p) p" using assms equiv_def by blast 
(* MC: for ?LH \<longrightarrow> ?RH, reflexivity suffices *)
ultimately also have "?LH \<longrightarrow> x \<in> p``{x}" using ll61 by fastforce
ultimately have 3: "?LH \<longrightarrow> ?RH" by force 
have "?r ?P = {p``{x}| x. x \<in> ?d p}" using l20 by metis then obtain xx where 
1: "X=p``{xx} & xx \<in> Domain p" using assms by auto
{
  assume ?RH hence "x \<in> p``{xx}" using assms 1 by metis
  hence "(xx,x) \<in> p" by fast hence "p``{x}=p``{xx}" using assms by (metis equiv_class_eq_iff)
  hence "(x,X) \<in> ?P" using 1 0 by auto
}
thus ?thesis using 3 by linarith
qed

lemma ll63: assumes "equiv (Domain p) p" "equiv (Domain q) q"
shows "quotient r p q = (projector p)^-1 O r O (projector q)"
proof -
let ?p=projector let ?P="?p p" let ?Q="?p q" let ?q=quotient let ?D=Domain
let ?PP="?P ^-1" let ?R=Range let ?LH="?q r p q" let ?RH="?PP O r O ?Q" have 
1: "\<forall> X\<in> ?D ?PP. \<forall> x. ((x \<in> X) = ((X,x) \<in> ?PP))" using ll62 assms(1) by fast have 
2: "\<forall> X\<in> ?R ?Q. \<forall> x. ((x \<in> X) = ((x,X) \<in> ?Q))" using ll62 assms(2) by fast
have "?RH = {(X,Y)| X Y. EX x y. (X,x) \<in> ?PP & (x,y) \<in> r & (y,Y)\<in> ?Q}" by blast
also have "... = 
{(X,Y)| X Y. EX x y. X \<in> ?D ?PP & (X,x) \<in> ?PP & (x,y) \<in> r & (y,Y)\<in> ?Q}" by force
also have "... = 
{(X,Y)| X Y. EX x y. X \<in> ?D ?PP & x \<in> X & (x,y) \<in> r & (y,Y)\<in> ?Q}" using 1 by auto
also have "... = 
{(X,Y)| X Y. EX x y. X \<in> ?D ?PP & x \<in> X & (x,y) \<in> r & Y \<in> ?R ?Q & y \<in> Y}" using 2 by auto
also have "... = {(X,Y)| X Y. X\<in> ?D ?PP & Y \<in> Range ?Q & X \<times> Y \<inter> r \<noteq> {}}" by auto
also have "... = {(X,Y)| X Y. X\<in> Range ?P & Y \<in> Range ?Q & X \<times> Y \<inter> r \<noteq> {}}" by auto
also have "... = quotient r p q" using quotient_def by fastforce
ultimately show ?thesis by presburger
qed

lemma ll51: "(P \<union> Q) outside X = P outside X \<union> (Q outside X)"
proof -
  let ?R="P \<union> Q" let ?r="Range" let ?rp="?r P" let ?rq="?r Q" let ?rr="?r ?R"
  have "?R - (X \<times> ?rr)= P - (X \<times> ?rr) \<union> (Q - (X \<times> ?rr))" by fast
  also have "... = P - (X \<times> ?rp) \<union> (Q - (X \<times> ?rr))" by blast
  also have "... = P - (X \<times> ?rp) \<union> (Q - (X \<times> ?rq))" by blast
  ultimately show ?thesis using Outside_def by metis
qed

lemma ll53: "(P +* Q) +* R = P +* (Q +* R)" (is "?LH = ?RH")
proof -
let ?D="Domain" let ?dp="?D P" let ?dq="?D Q" let ?dr="?D R" have 
"?LH=(P outside ?dq \<union> Q) outside ?dr \<union> R" using paste_def by metis also have 
"...= ((P outside ?dq) outside ?dr) \<union> (Q outside ?dr) \<union> R" using ll51 by metis
also have "...= (P outside (?dq \<union> ?dr)) \<union> (Q outside ?dr) \<union> R" using ll52 by metis 
also have "...= (P outside (?D (Q +* R))) \<union> (Q +* R)" using paste_def 
by (metis Domain_Un_eq paste_Domain sup_assoc sup_commute sup_left_commute)
ultimately show ?thesis using paste_def by blast
qed

lemma ll80: "\<Union> (kernel R) = Domain R" 
proof -
have "\<Union> {R^-1 `` {y}|y. y\<in> Range R} = Domain R" by blast
thus ?thesis using ll65 by metis
qed

lemma ll85: assumes "runiq f" shows "runiq (f^-1 O f)"
proof -
let ?g="f^-1" let ?it="?g O f" have "\<forall> Y. f``(?g``Y) = ?it``Y" by fast
thus ?thesis using ll70 assms runiq_def by metis
qed

lemma ll94: "graph (Range R) id \<subseteq> (R^-1 O R)"
proof -
let ?r=Range {fix z assume "z \<in> graph (?r R) id" hence 
  "z \<in> {(x, id x)|x . x \<in> ?r R}" using graph_def by blast then obtain x where
  0: "z = (x, id x) & x \<in> ?r R" by fast
  have "z \<in> R^-1 O R" using 0 by auto }
thus ?thesis by blast
qed

lemma ll86: assumes "runiq f" shows "f^-1 O f = graph (Range f) id"
proof -
let ?p=projector let ?k=kernel let ?u=part2rel let ?d=Domain let ?r=Range
let ?G=Graph let ?i="?G id" let ?I="?p ?i" let ?u=runiq let ?g=graph
let ?if="f^-1" let ?II="?if O f" have "?d ?II \<subseteq> ?r f" by fast
also have "?d (?g (?r f) id) \<supseteq> ?r f" using graph_def by fast
ultimately have "?d ?II \<subseteq> ?d (?g (?r f) id)" by auto
moreover have "?g (?r f) id \<subseteq> ?II" using ll94 by blast
moreover have "?u ?II" using assms(1) ll85 by fast
ultimately show "?II = ?g (?r f) id" using ll81 by metis
qed

lemma ll90: "(\<Union> ((projector R)``X)) \<supseteq> R``X" using projector_def by blast

lemma ll89: (*fixes X::"'a set" fixes R::"('a \<times> 'b) set" shows *)
"\<Union> ((projector R)``X) \<subseteq> R``X" unfolding projector_def by fast

corollary ll91: shows "(\<Union> ((projector R)``X)) = R``X" using ll90 ll89 
assms by (metis antisym_conv)

lemma ll87: "runiq ((projector Id)^-1)"
proof -
let ?u=runiq let ?p=projector let ?i=Id let ?I="?p ?i" let ?Ii="?I^-1"
let ?f="{(x,{x})|x. x\<in>UNIV}" let ?g="?f^-1" have "?g={({x},x)|x. x\<in>UNIV}" by blast
moreover have "... = {(X, the_elem X)|X. X \<in> finestpart UNIV}" using finestpart_def by fastforce
also have "runiq ..." using l14 by fast finally have "runiq ?g" by blast
also have "?I=?f" using projector_def by auto ultimately show "runiq ?Ii" by metis
qed

lemma ll92: "Range ((projector Id)^-1)=UNIV" using projector_def by fastforce

corollary ll93: "(((projector Id) ^-1)^-1) O ((projector Id) ^-1)=graph UNIV id"
using ll86 ll87 ll92 by metis

corollary ll95: "Graph id=Id & Id=graph UNIV id" unfolding graph_def Graph_def by auto 

corollary ll96: "(projector Id) O ((projector Id)^-1) = Id" using ll93 ll95 by fastforce

corollary ll25: "(P +* Q) `` (Domain Q - X) = Q``(Domain Q - X)"
using ll50 by (metis Int_Diff inf_idem)

lemma "sym (graph X id)" unfolding graph_def sym_def by force

lemma ll02: assumes "runiq f" "runiq g" shows "runiq (f O g)" using assms by (metis relcomp_Image runiq_def)

lemma ll04: assumes "runiq P" shows "projector (P O Q) = P O (projector Q)"
using assms eval_runiq_rel Image_runiq_eq_eval ll71 ll02 l15
ll81 projector_def 
(*TODO@MC: modularize this proof *)
proof -
let ?u=runiq let ?t=trivial let ?k=kernel let ?c=part2rel 
let ?d=Domain let ?r=Range let ?G=Graph let ?g=graph let ?p=projector
let ?pp="%R.{ (x,R``{x}) | x . x \<in> ?d R}" have 
10:"{(x, P,,x)|x. x\<in> P^-1``(?d Q)} \<subseteq> P" using assms eval_runiq_rel by fast
have "\<forall> X. (%x. P,,x)`(?d P \<inter> X)=P``(?d P \<inter> X)" 
using Image_runiq_eq_eval assms by fast 
moreover have "\<forall> Y. ?d P \<inter> P^-1``Y=P^-1``Y" by fast
ultimately have "\<forall>Y. (%x. P,,x)`(P^-1``Y)=P``(P^-1``Y)" by metis 
hence "\<forall>Y. (%x. P,,x)`(P^-1``Y) \<subseteq> Y" using assms ll71 by metis hence 
9:"{(y,Q``{y})|y. y\<in>(%x. P,,x)`(P^-1``(?d Q))} \<subseteq> ?pp Q" by blast
have "?pp (P O Q) = {(x, Q ``(P``{x}))| x. x \<in> P^-1``(?d Q)}" by fast
also have "... = {(x, Q``{P,,x})|x. x\<in>P^-1``(?d Q)}"
using Image_runiq_eq_eval assms by force
also have "... = {(x, P,,x)|x. x\<in> P^-1``(?d Q)} O 
{(y,Q``{y})|y. y\<in>(%x. P,,x)`(P^-1``(?d Q))}" by blast
also have "... \<subseteq> {(x, P,,x)|x. x\<in> P^-1``(?d Q)} O (?pp Q)" using 9 by force
also have "... \<subseteq> P O (?pp Q)" using 10 by blast
also have "runiq ..." using assms ll02 l15 by (metis projector_def)
ultimately have "?pp (P O Q) \<subseteq> P O (?pp Q) & runiq (P O (?pp Q))" by fastforce
also have "?d (?pp (P O Q)) \<supseteq> ?d (P O (?pp Q))" by auto
ultimately have "?pp (P O Q) = P O (?pp Q)" using ll81 by (metis projector_def)
thus ?thesis using projector_def by metis
qed

lemma ll01: "part2rel (kernel R)={(x1, x2)|x1 x2 . EX y. {x1,x2} \<subseteq> R^-1``{y}}"
proof -
let ?k=kernel let ?c=part2rel let ?d=Domain let ?r=Range
have "?c (?k R) = 
\<Union> ((% x . (x \<times> x)) ` {R^-1 `` {y}| y::'b. y\<in> ?r R})" using ll65 part2rel_def by metis
(*also have "... = \<Union> {R^-1``{y} \<times> (R^-1``{y})| y. y \<in> ?r R}" by auto
also have "... = 
{(x1, x2)|x1 x2 . EX y. (y \<in> (?r R) & x1 \<in> R^-1``{y} & x2 \<in> R^-1``{y})}" by blast
also have "... = 
{(x1, x2)|x1 x2 . EX y. (x1 \<in> R^-1``{y} & x2 \<in> R^-1``{y})}" by blast
 also have "... = {(x1, x2)|x1 x2 . EX y. {x1,x2} \<subseteq> R^-1``{y}}" by force*)
then show ?thesis by auto
qed

lemma ll03: "(part2rel (kernel R)) =  R O (R^-1)" using ll01 by auto

corollary ll05: assumes "runiq f" shows 
"f O (projector (f^-1)) = projector (part2rel (kernel f))"
using assms ll03 ll04 by metis

lemma ll16: "(P +* Q) outside (Domain Q) \<supseteq> P outside (Domain Q)" 
using assms paste_def l37 ll51 Un_commute Un_upper2 by metis

lemma ll17: "Domain (P outside (X \<union> Domain P)) \<subseteq> {}" 
by (metis Diff_subset_conv Un_upper2 le_supI1 outside_reduces_domain)

lemma ll18: "P outside (X \<union> Domain P)={}" using ll17 by fast

lemma ll19: "(P +* Q) outside (X \<union> Domain Q) = 
P outside (X \<union> Domain Q)" using assms paste_def ll51 ll52 ll18 
(* by (metis outside_union_restrict restrict_empty sup.right_idem)*)
by (metis (hide_lams, no_types) empty_subsetI le_sup_iff subset_refl sup_absorb1 sup_absorb2)

lemma ll12: assumes "runiq f" shows 
"Range (projector (f^-1)) = Range (projector (part2rel (kernel f)))"
(is "?A=?B")
proof -
(*TODO@MC: modularize & clean this proof *)
let ?r=Range let ?d=Domain let ?pp=projector let ?cc=part2rel let ?kk=kernel
let ?k="%R. {R^-1 `` {y}| y. y\<in> ?r R}"
let ?p="%R. {(x,R``{x})|x. x \<in> Domain R}"
let ?c="%X. \<Union> ((% x . (x \<times> x)) ` X)"
let ?ck="%R. {(x1, x2)|x1 x2 . EX y. {x1,x2} \<subseteq> R^-1``{y}}"
let ?if="f^-1"
let ?RH="{(x, f^-1``(f``{x}))| x::'a. x\<in>?d f}"
let ?LH="{(y, f^-1``{y})|y. y\<in> ?r f}"
let ?L="{f^-1``{y}|y. y\<in> ?r f}"
let ?R="{f^-1``(f``{x})|x. x\<in>?d f}"
have "?L={f^-1``z|z. EX y. y\<in>?r f & z={y}}" by auto
moreover have "...={f^-1``zz|zz. zz\<in>{z. EX y. y\<in>?r f & z={y}}}" by auto
ultimately have
11: "?L={f^-1``zz|zz. zz\<in>{z. EX y. y\<in>?r f & z={y}}}" by presburger
have "?R={f^-1``z|z. EX x. x\<in>?d f & z=f``{x}}" by blast
moreover have "...={f^-1``zz|zz. zz\<in>{z. EX x. x\<in>?d f & z=f``{x}}}" by auto
ultimately have
12: "?R={f^-1``zz|zz. zz\<in>{z. EX x. x\<in>?d f & z=f``{x}}}" by presburger
have 
2: "\<forall>y. (y\<in>?r f \<longleftrightarrow> (EX x.(x\<in>?d f & {y} \<subseteq> f``{x})))" using assms 
by auto
moreover have 
3: "\<forall>x y. {y} \<subseteq> f``{x} \<longrightarrow> {y}=f``{x}" using assms runiq_def SetUtils.ll10 SetUtils.ll11 by metis
ultimately have 
"\<forall>y. (y\<in>?r f \<longleftrightarrow> (EX x.(x\<in>?d f & {y} = f``{x})))" by blast
then have "{z. EX y. y\<in>?r f & z={y}} = 
{z. EX x y. x\<in>?d f & y\<in>?r f & z={y} & {y}=f``{x}}" by auto
moreover have "... = {z. EX x y. x\<in>?d f & z = f``{x}}" using 3 by fast
moreover have "{z. EX x y. x\<in>?d f & z = f``{x}} = {z. EX x . x\<in>?d f & z = f``{x}}" 
by auto
ultimately have "{z. EX y. y\<in>?r f & z={y}}={z. EX x. x\<in>?d f & z=f``{x}}" by presburger
hence 
4: "?L=?R" using 11 12 by presburger have 
1: "?pp=?p" using  projector_def by metis
then have "?A=?r (?p ?if)" by (rule HOL.arg_cong)
moreover have "... = ?L" by auto ultimately have 
5: "?L=?A" by presburger
have "?kk=?k" using ll65 by metis
moreover have "?cc=?c" using part2rel_def by auto
ultimately have "?B=?r(?p (?c (?k f)))" using 1 by metis
moreover have "?ck f = (?c (?k f))" using ll01 by auto
moreover have "?R=?r (?p (?ck f))" by auto
ultimately have "?B=?R" by presburger
thus ?thesis using 4 5 by presburger
qed

lemma ll13: "Domain (projector R)=Domain R" unfolding projector_def by blast

lemma ll14: assumes "x\<in>Domain f" "runiq f" shows "f,,x \<in> Range f"
using assms by (metis Range_iff eval_runiq_rel)

lemma ll34: "graph X f \<subseteq> (graph (X \<union> Y) f)" unfolding graph_def by blast

definition functional where "functional X = (\<forall>x \<in> X. runiq x)"
(*MC: Alternatively, say X \<subseteq> runiqs *)

abbreviation cartesian where  
"cartesian X R x == (\<forall>y. (R+*({x}\<times>{y})\<in>X))"
(*
"cartesian a = (\<forall> b i y. ((b \<in> Domain a 
& i \<in> Domain b)
(*& Domain b = Domain bb*)
\<longrightarrow> b +* ({i} \<times> {y}) \<in> Domain a))"
*)

lemma ll38: assumes "runiq f" shows "cartesian runiqs f x"
proof -
  let ?U=runiqs let ?u=runiq let ?g=graph let ?c=cartesian
  {
    fix y::'b have "?u (f+*({x}\<times>{y}))"  
    using assms runiq_singleton_rel runiq_paste2 by fastforce
    hence "f +* ({x}\<times>{y})\<in>?U" using runiqs_def by fast
  }
  thus ?thesis by fast
qed

corollary ll39: assumes "runiq f" shows "cartesian (Domain (graph runiqs F)) f x"
using ll38 ll37 assms by metis

lemma lll03: "P outside X \<subseteq> P outside (X \<inter> Domain P)" 
using Outside_def Diff_Int Sigma_Int_distrib1 sup_ge1 by metis

lemma lll04: "(P || X) outside Y = P || (X-Y)" using restrict_def
lll02 by (metis Diff_Compl double_complement outside_reduces_domain lll00 lll01)

lemma lll06: "(P outside (X \<union> Y)) \<inter> (Q || (X \<inter> Z)) = {}" 
using lll06c by (metis (hide_lams, no_types) inf_commute lll02)

lemma lll71: "(P +* Q)||X = (P||X) +* (Q||X)" 
proof -
  let ?R="P+*Q" let ?d=Domain let ?dQ="?d Q" have 
  "?R || X = ((P outside ?dQ) || X) \<union> (Q || X)" using lll40 by (metis paste_def) moreover 
  have "(P outside ?dQ) || X = P ||(X - ?dQ)" 
unfolding restrict_def Outside_def 
(* using  
Domain_Un_eq inf_sup_aci(5) ll52 lll00 lll04 outside_reduces_domain paste_Domain paste_def *)
by blast  
  moreover have "... = P || (X - (X \<inter> ?dQ))" by (metis Diff_Int_distrib Int_Diff Int_absorb)
  moreover have "... = (P || X) outside (X \<inter> ?dQ)" by (metis lll04)
  ultimately show ?thesis by (metis Int_commute ll41 paste_def)
qed

lemma lll72: "(P +* Q) outside X = (P outside X) +* (Q outside X)" by (metis (hide_lams, no_types) 
Un_Diff_cancel Un_commute ll51 ll52 outside_reduces_domain paste_def)

lemma lll73: assumes "runiq f" shows "runiq (f +< (x,y))" using runiq_paste2 assms
runiq_singleton_rel by metis

lemma lll43: "(X2 \<times> {y}) outside X1 = (X2 - X1) \<times> {y}" using assms Outside_def 
by auto

corollary lll91b: "(P +* Q) outside (Domain Q)=P outside (Domain Q)" using ll19 by (metis Un_absorb)

corollary lll91c: "(P +< (x,y)) -- x = P -- x" using lll91b by (metis Domain_empty Domain_insert fst_conv)

lemma lll89: "P +< (x,y) = P +* {x}\<times>{y}" by simp

corollary ll50b: "(P +* ({x}\<times>{y})),,x=y"
proof -
  let ?f="{x}\<times>{y}" let ?d=Domain have "?d ?f={x}" by simp 
  then have "(P +* ?f)``{x}=?f``{x}" using ll50 subset_refl inf_absorb2 by metis
  moreover have "...={y}" by fast ultimately show ?thesis by simp
qed

corollary lll93: "{R+<(x,y)| y. True} = {(R +< (x,yy)) +< (x,y)| y. True}"
using assms by (metis (hide_lams, no_types) Domain_empty Domain_insert lll91c paste_def surjective_pairing)

corollary lll94: "cartesian X R x = ({R+<(x,y)| y. True} \<subseteq> X)" by auto

corollary lll93b: "({R+<(x,y)| y. True} \<subseteq> X) = ({(R+<(x,yy))+<(x,y)| y. True} \<subseteq> X)"
using lll93 by metis

corollary lll93c: "(cartesian X R x)=(cartesian X (R+<(x,yy)) x)" (is "?lh=?rh") 
using lll93b lll94 snd_conv lll93 
proof -
  have "?lh = ({R+<(x,y)| y. True} \<subseteq> X)" using lll93 by auto
  moreover have "... = ({(R+<(x,yy))+<(x,y)| y. True} \<subseteq> X)" using lll93 by metis
  ultimately show ?thesis using lll94 by auto
qed
lemma lll07: "(P \<inter> Q)``{x} = (P``{x} \<inter> (Q``{x}))" by fastforce
end

