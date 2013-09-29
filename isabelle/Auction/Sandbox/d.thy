theory d

imports c SEQ 

begin

lemma ll16: shows "(P +* Q) outside (Domain Q) \<supseteq> P outside (Domain Q)" 
using assms paste_def Outside_def l38 l37 ll51 by (smt Un_commute Un_upper2)

lemma ll17: shows "Domain (P outside (X \<union> Domain P)) \<subseteq> {}" 
by (metis Diff_subset_conv Un_upper2 le_supI1 outside_reduces_domain)

lemma ll18: shows "P outside (X \<union> Domain P)={}" using ll17 by fast

lemma ll19: shows "(P +* Q) outside (X \<union> Domain Q) = 
P outside (X \<union> Domain Q)" using assms paste_def ll51 ll52 ll18 
(* by (metis outside_union_restrict restrict_empty sup.right_idem)*)
by (metis (hide_lams, no_types) empty_subsetI le_sup_iff subset_refl sup_absorb1 sup_absorb2)

definition cartesian where 
(*TODO@MC: make apply cartesian to Domain a, rather than to a itself 
Also consider moving i as an argument: cartesian i a = ...
*) 
"cartesian a = (\<forall> b i y. ((b \<in> Domain a 
& i \<in> Domain b)
(*& Domain b = Domain bb*)
\<longrightarrow> b +* ({i} \<times> {y}) \<in> Domain a))"

lemma ll57: fixes a::real fixes b c shows "a*b - a*c=a*(b-c)"
using assms by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

type_synonym price = real
type_synonym allocation = real
type_synonym index = nat
type_synonym bid = "(index \<times> price) set"
definition prices where "prices = \<real>"
definition allocations where "allocations = \<real>"
definition indices where "indices = \<nat>"
(* MC: have to investigate what entities we require 
the currency and the allocation values to be represented by.
Rational and Reals will do, but I guess sub{rings,fields} of a field with 
some order and topology will be sufficient to prove Maskin2. 
Mathematically, this is probably the most interesting issue;
not sure whether there is enough Isabelle library
to tackle that, so for the moment let's stick to \<rat>, \<real>. *)

definition weakdomgen
(* ::"index => (bid \<times> allocation) set => (bid \<times> price) set => bool" *)
where "weakdomgen P i a p = ( \<forall> b::bid . 
\<forall> Y. (P Y) \<longrightarrow>  
(EX f. f (a,, b) - (p,, b) \<le> f (a,, (b+* ({i} \<times> Y))) - (p,, (b+*({i} \<times> Y))))
(* \<forall> r::price . 
r* (a,, b)-(p,, b) \<le> r* (a,, (b+* ({i}\<times>{r}))) - p,, (b+* ({i}\<times>{r}))*)
)" 

definition weakdom
(* ::"index => (bid \<times> allocation) set => (bid \<times> price) set => bool" *)
where "weakdom i a p = 
( \<forall> b::bid .\<forall> Y. 
(Y \<noteq> {} & {b, b+*({i}\<times>Y)} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b) \<longrightarrow> 
(EX y.(y (a,, b))-(p,, b) \<le> y (a,, (b+* ({i}\<times>Y))) - (p,, (b+* ({i}\<times>Y)))
))"
(*MC: Later, we will require a or p to be defined only on runiq bids, 
so that R must be a singleton and we can use r=the_elem R *)
(* MC: The problem here is the multiplication of a price (r) 
and an allocation. 
They should be allowed to be of different subtypes (e.g., real and nat) of 
a supertype admitting multiplication, order and subtraction.
In Mizar, the clustering+type widening mechanism makes such things painless.
What about Isabelle? *)

definition dom2 where "dom2 i a p = 
(EX f::(price set => allocation => price). \<forall> b::bid. \<forall> Y. ({b, b+*({i}\<times>Y)} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b
\<longrightarrow>
(f Y (a,, b))-(p,, b) \<le> (f Y (a,, (b+* ({i}\<times>Y)))) - (p,, (b+* ({i}\<times>Y)))
)
)"
(* Stronger than above: we require that the function to obtain y 
is independent of b and Y *)

definition dom3 where "dom3 i a p = (
\<forall> b::bid. \<forall> Y. {b, b +* ({i} \<times> Y)} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b \<longrightarrow>(
the_elem Y*(a,, b) - (p,, b)) \<le> 
the_elem Y*(a,, (b+* ({i} \<times> Y))) - (p,, (b+* ({i}\<times>Y))))"

definition dom4 where "dom4 i a p = (
\<forall> b::bid. \<forall> v. ({b, b+* ({i}\<times>{v})} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b) \<longrightarrow>
v*(a,,b)-(p,,b) \<le> v*(a,,(b+*({i}\<times>{v})))-(p,,(b+*({i}\<times>{v}))))"

definition functional where "functional X = (\<forall>x \<in> X. runiq x)"

lemma ll23: assumes "functional (Domain a)" assumes "dom4 i a p" shows "weakdom i a p" 
proof -
let ?d=Domain let ?u=runiq let ?t=trivial 
  {
  fix b::bid fix Y let ?bv="b+*({i}\<times>Y)" let ?v="the_elem Y" let ?y="%x. ?v*x" assume 
  1: "Y\<noteq>{} & {b, ?bv}\<subseteq>(?d a \<inter>(?d p)) & i\<in>?d b" then have 
  "{i} \<subseteq> ?d ({i}\<times>Y)" by blast then have 
  "?bv``{i} \<supseteq> ({i} \<times> Y)``{i}" using paste_def 
  by (metis (full_types) Image_mono Un_commute Un_upper1 subset_refl)
  also have "({i} \<times> Y)``{i} = Y" by blast 
  also have "?u ?bv" using assms functional_def 1 by blast
  ultimately have "?t Y" using l32 by (metis trivial_subset) hence 
  2: "Y={?v}" using 1 by (metis subset_singletonD trivial_def) then have 
  "?v*(a,,b)-(p,,b)\<le>?v*(a,,(b+*({i}\<times>{?v})))-(p,,(b+*({i}\<times>{?v})))" 
  using 1 assms dom4_def by metis hence "EX y.
  (y (a,,b))-(p,,b)\<le>y (a,,(b+*({i}\<times>Y)))-(p,,(b+*({i}\<times>Y)))" using 2 by auto
}
thus ?thesis using weakdom_def by metis
qed

definition runiqs where "runiqs={f. runiq f}"

definition reducedbid 
:: "index => (bid \<times> allocation) set => 
(bid \<times> index set \<times> bid \<times> allocation) set" 
where
"reducedbid i a = {(b, (Domain b, b outside {i}, a ,, b))| b. b \<in> Domain a}
(*Graph (% b . ((b outside {i}, a ,, b)))*)
"

lemma l24: fixes p::"(bid \<times> price) set" 
(*MC: Why do I need to make this type explicit?*) 
fixes i a
assumes "Domain a \<subseteq> Domain p" "weakdom i a p" "runiq p" shows 
"compatible p (part2rel (kernel (reducedbid i a))) (Graph id)" 
proof - (* see LaTeX *)
let ?w="weakdom" let ?R="reducedbid i a" let ?r="runiq" let ?I="Graph id"
let ?e="kernel ?R" let ?E="part2rel ?e" let ?d=Domain let ?k=kernel
let ?f="%x. (x outside {i}, a ,, x)" let ?P="%x. True" let ?RR="{(x, ?f x)| x. ?P x}"
have "?d ?E = ?d ?R" using l47 ll80 by metis
also have "... = ?d a" using reducedbid_def by blast ultimately have 
"?d ?E = ?d a & ?d ?R=?d a" by force 
also have "?r ?R" using reducedbid_def l14 by force ultimately have 
1: "?r ?R & ?d ?E = ?d a & ?d ?R=?d a" by force 
{
  fix b let ?LH="p``(?E``{b})" let ?RH="?I``(p``{b})" let ?Y="b `` {i}"
  assume "b \<in> Domain ?E" hence 
  15: "b \<in> Domain a & b \<in> Domain p" 
  using 1 assms(1) by blast
have 
  17: "?RH=p``{b}" by (metis (hide_lams, no_types) Image_outside_domain `runiq p` all_not_in_conv disjoint_iff_not_equal l5 runiq_def subsetI subset_singletonD the_elem_eq trivial_def)
  {
    fix pp assume "pp \<in> ?LH" then obtain bb where
    10: "(bb, pp) \<in> p & bb \<in> ?E``{b}" using Image_def by blast
    let ?YY="bb `` {i}"
    have "?P bb" by fast hence 
    11: "?RR ,, bb = ?f bb" by (rule l16) 
    have "(b,bb) \<in> part2rel (kernel ?R)" 
    using 10 kernel_def part2rel_def eval_rel_def ll73 by force
    also have "(b,bb) \<in> part2rel (?k ?R)=(EX Z. Z\<in>(?k ?R) & b \<in> Z & bb \<in> Z)" 
    using ll73 by (rule Extraction.exE_realizer)
    ultimately have "EX X. X\<in>(?k ?R) & b \<in> X & bb \<in> X" by fast
    also have "?k ?R={?R^-1 `` {y}| y. y \<in> Range ?R}" using ll65 by blast
    ultimately obtain y where 
    19: "y \<in> Range ?R & b \<in> ?R^-1``{y} & bb \<in> ?R^-1``{y}" by auto
    have "bb \<in> ?d ?R" using 10 1 19 by blast
    hence "bb \<in> ?d a & bb \<in> ?d p" using assms(1) 1 by blast hence 
    16: "{b, bb} \<subseteq> ?d a \<inter> (?d p)" using 15 by auto
    have "?R``{b} \<inter> ?R``{bb} \<noteq> {}" using 19 by blast
    hence "(?d b,b outside {i}, a ,, b) = (?d bb,bb outside {i}, a ,, bb)"
    using reducedbid_def Image_def by force hence 
    2: "?d b = ?d bb & b outside {i} = bb outside {i} & a,,b=a,,bb" by fast
    hence "i \<notin> ?d b \<longrightarrow> bb outside {i}=bb" using Outside_def by auto
    also have "i \<notin> ?d b \<longrightarrow> b outside {i}=b" using Outside_def by blast
    ultimately have 
    7: "i \<notin> ?d b \<longrightarrow> bb=b" using 2 by force
    {
      assume "i \<in> ?d b" hence
      "i\<in> ?d b & ?YY \<noteq> {} & b``{i} \<noteq> {}" using 2 by blast then have 
      14:"i \<in> ?d b & ?YY \<noteq> {} & ?d ({i} \<times> ?YY) = {i} & ?d ({i} \<times> (b``{i})) = {i}" 
      by blast
      also have "bb=(bb outside {i}) +* ({i} \<times> ?YY)" by (metis paste_outside_restrict restrict_to_singleton)
      also have "... = (b outside {i}) +* ({i} \<times> ?YY)"  using 2 by presburger
      also have "... = (b outside (Domain ({i} \<times> ?YY))) +* ({i} \<times> ?YY)" 
  using 14 by presburger
      also have "... = b +* ({i} \<times> ?YY)"
      using paste_def by (metis l37)    
      ultimately have 
      20: "bb=b +* ({i} \<times> ?YY) & i \<in> ?d b & {b, b+*({i} \<times> ?YY)} \<subseteq> ?d a \<inter> (?d p)
      & ?YY \<noteq> {}"
      using 16 by (metis `(b outside {i}) +* {i} \<times> bb \`\` {i} = (b outside Domain ({i} \<times> bb \`\` {i})) +* {i} \<times> bb \`\` {i}` `(bb outside {i}) +* {i} \<times> bb \`\` {i} = (b outside {i}) +* {i} \<times> bb \`\` {i}` `bb = (bb outside {i}) +* {i} \<times> bb \`\` {i}`)
      then obtain y where 
      18: "(y (a,, b))-(p,, b) \<le> y (a,, (b+* ({i}\<times>?YY))) - (p,, (b+* ({i}\<times>?YY)))"
      using weakdom_def assms(2) by metis    
      have "(y (a,, b)) - (p,,b) \<le> y (a,, bb) - (p,, bb)" using 18 20 by force hence 
      5: "- (p,,b) \<le> - (p,,bb)" using 2 by auto
      have "bb +* ({i} \<times> (b``{i})) = b +* (({i} \<times> (bb``{i})) +* ({i} \<times> (b``{i})))" using 20 ll53 by metis
      also have "{i} \<times> (bb `` {i}) +* ({i} \<times> (b ``{i})) = {i} \<times> (b``{i})" 
      using paste_def 14 by (smt Diff_cancel Domain_empty_iff Un_commute Un_empty_right outside_reduces_domain)
      (* ll56 not needed?! *)
      ultimately have "bb +* ({i} \<times> (b``{i})) = b +* ({i} \<times> (b``{i}))" by auto
      also have "...= b" using ll84 by fast
      ultimately have "b=bb +* ({i} \<times> (b``{i}))" by simp hence 
      4: "b= bb +* ({i} \<times> (b``{i})) & i \<in> ?d bb & {bb, bb+*({i} \<times> (b``{i}))} \<subseteq> ?d a \<inter> (?d p)
      & b``{i} \<noteq> {}"
      using 20 16 2 by force 
      then obtain yy where 
      3: "(yy (a,, bb))-(p,, bb) \<le> yy (a,, (bb+* ({i}\<times>(b``{i})))) - (p,, (bb+* ({i}\<times>(b``{i}))))"
      using weakdom_def assms(2) by metis    
      have "(yy (a,, bb)) - (p,,bb) \<le> yy (a,, b) - (p,, b)" using 3 4 by force
      hence "- (p,,bb) \<le> - (p,,b)" using 2 by auto
      hence "p,,b = p,,bb" using 5 by linarith
      hence "p,, b = p,, bb & runiq p & b \<in> ?d p & bb \<in> ?d p" using 2 assms(3) 16 by force
      hence "p``{b} = p``{bb}" by (metis Image_runiq_eq_eval)
    }
    hence "pp \<in> p``{b}" using 10 7 by fast
  }
  hence "?LH \<subseteq> ?RH" using 17 by auto
}
thus ?thesis using compatible_def by force
qed 

corollary ll21: fixes p::"(bid \<times> price) set"
assumes "Domain a \<subseteq> Domain p" "weakdom i a p" "runiq p"
shows "runiq (quotient p (part2rel (kernel (reducedbid i a))) Id)"
proof -
let ?Id="Graph id" let ?d=Domain let ?u=runiq let ?q=quotient let ?c=compatible
let ?w="weakdom i a p"
let ?b="reducedbid i a" let ?p="part2rel (kernel ?b)"
have "?d a \<subseteq> ?d p & ?w & ?u p" using assms by fast
then have "?c p ?p ?Id" using l24 by auto
have "?u ?b" using l14 reducedbid_def by force then
have "equiv (?d ?p) ?p" using ll78 assms by (metis l47 ll80)
moreover have "?Id=Id & equiv (?d Id) Id" using ll95 equiv_def Id_def Domain_Id refl_Id sym_Id trans_Id
by metis
moreover have "?c p ?p ?Id" using l24 assms by blast
ultimately show "?u (?q p ?p Id)" using l23 equiv_def assms by metis
qed

definition quotientbid where "quotientbid i a = part2rel (kernel (reducedbid i a))"

definition Quotientbid where "Quotientbid i a = projector (quotientbid i a)"

lemma ll09: fixes i a shows "Domain (reducedbid i a) = Domain a 
& Domain a=Domain (quotientbid i a) 
& Domain a = Domain (projector (quotientbid i a))
& runiq (reducedbid i a)"
proof -
let ?d=Domain let ?b="reducedbid i a" let ?B="quotientbid i a" let ?p=projector
have "?d a= ?d ?b" using reducedbid_def by blast
also have "... = ?d ?B" using quotientbid_def by (metis l47 ll80)
moreover have "... = ?d (?p ?B)" using projector_def by blast
moreover have "runiq ?b" using reducedbid_def l14 by force
ultimately show ?thesis by presburger
qed

lemma ll10: shows "trivial {x}" by (metis order_refl the_elem_eq trivial_def)

lemma ll11: assumes "trivial X" "{x} \<subseteq> X" shows "{x}=X" 
using singleton_sub_trivial_uniq assms by (metis subset_antisym trivial_def)

lemma ll12: fixes f::"('a \<times> 'b) set" assumes "runiq f" shows 
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
3: "\<forall>x y. {y} \<subseteq> f``{x} \<longrightarrow> {y}=f``{x}" using assms runiq_def ll10 ll11 by metis
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

lemma ll13: shows "Domain (projector R)=Domain R" 
proof -
let ?d=Domain let ?p="%R. {(x,R``{x})|x. x \<in> ?d R}"
have "?d (?p R)=?d R" by blast thus ?thesis using projector_def by metis
qed

lemma ll14: assumes "x\<in>Domain f" "runiq f" shows "f,,x \<in> Range f"
using assms by (metis Range_iff eval_runiq_rel)

lemma ll15: shows "quotient p (quotientbid i a) Id = 
(projector (quotientbid i a))^-1 O p O (projector Id)"
using ll63 by (metis R_O_Id comp_equivI converse_Id ll09 ll78 quotientbid_def)

lemma ll07: fixes a i p b 
assumes "runiq (quotient p (quotientbid i a) Id)" 
"b \<in> Domain (projector (quotientbid i a))" 
"Domain (projector (quotientbid i a)) \<subseteq> Domain p"
shows "p``{b} = 
((projector ((reducedbid i a)^-1)) O (quotient p (quotientbid i a) Id) O ((projector Id)^-1))
``((reducedbid i a)``{b})"
proof -
let ?u=runiq let ?t=trivial let ?k=kernel let ?c=part2rel let ?i="Graph id"
let ?d=Domain let ?r=Range let ?G=Graph let ?g=graph let ?p=projector
let ?rb=reducedbid let ?ri="?rb i a" 
let ?e="quotientbid i a" let ?E="?p ?e" 
let ?P="quotient p ?e ?i" let ?IE="?E^-1"
have "runiq ?ri" using l14 reducedbid_def by force then
have "equiv (?d  ?ri) (part2rel (kernel ?ri))" using ll78 by fast
then have "equiv (?d ?e) ?e" 
using quotientbid_def by (metis (full_types) comp_equivI equiv_comp_eq)
also have "equiv (?d Id) Id" using equiv_def Id_def 
by (metis Domain_Id refl_Id sym_Id trans_Id)
ultimately have "?P=?IE O p O (?p Id)" using ll63 ll95 by metis
hence "?P O ((?p Id)^-1)=?IE O p O ((?p Id) O ((?p Id)^-1))" by auto
also have "...=?IE O p O Id" using ll96 by metis
also have "...=?IE O p" by auto ultimately have 
1: "?IE O p = ?P O ((?p Id)^-1)" by presburger have 
2: "?u (?IE O p)" using assms(1) ll95 ll87 ll02 1 by metis
have "?u ?E" using l15 by fast
also have "?u ?ri" using reducedbid_def l14 by force ultimately have 
0: "b \<in> ?d ?E & ?u ?E & p``{b} \<noteq> {} & ?u ?ri" using assms l15 l14 by blast
then have "p``{b} \<subseteq> p`` ((?E O ?IE)``{b})" by fast
also have "... = p `` (?IE `` (?E ``{b}))" by blast
also have "... \<subseteq> p `` (?IE `` {?E ,, b})" using 0 by (metis (hide_lams, no_types) Image_runiq_eq_eval subset_refl)
also have "... = (?IE O p) `` {?E,,b}" by fast
ultimately have "p``{b} \<subseteq> (?IE O p)``{?E,,b} & ?t ((?IE O p)``{?E,,b})"
using 2 runiq_def by (metis (hide_lams, no_types) l32)
then also have "p``{b} \<supseteq> (?IE O p)``{?E,,b}" using 0 trivial_def by (metis (hide_lams, no_types) equals0D subsetI subset_singletonD)
ultimately have "p``{b} = (?IE O p)``{?E,,b}" by fastforce
moreover have "...= (?P O ((?p Id)^-1)) ``{?E,,b}" using 1 by force
finally have "p``{b} = (?P O ((?p Id)^-1)) ``{?E,,b}" by fast
also have "... = (?P O ((?p Id)^-1)) ``(?E``{b})" using 0 by 
(metis (hide_lams, no_types) "1" Image_runiq_eq_eval calculation insert_compr l15 quotientbid_def)
also have "... = (?P O ((?p Id)^-1)) `` (?p (?c (?k ?ri))``{b})"
using quotientbid_def by presburger
also have "... = (?P O ((?p Id)^-1)) `` (?ri O (?p (?ri^-1)))``{b}" 
using ll05 0 by metis
also have "... = (?P O ((?p Id)^-1)) `` (?p (?ri^-1))``(?ri``{b})" by blast 
also have "... = ((?p (?ri^-1)) O (?P O ((?p Id)^-1)))``(?ri``{b})" by blast
also have "... = ((?p (?ri^-1)) O ?P O ((?p Id)^-1))``(?ri``{b})" by fast
ultimately show ?thesis using ll95 by metis
qed

corollary ll08: fixes a b i p
assumes "runiq (quotient p (quotientbid i a) Id)"
"runiq p"
"b \<in> Domain a" "Domain a \<subseteq> Domain p"
shows
"p,,b = 
((projector ((reducedbid i a)^-1)) O (quotient p (quotientbid i a) Id) O ((projector Id)^-1))
,, (reducedbid i a,,b)"
proof -
(*TODO@MC: modularize&clean *)
let ?u=runiq let ?t=trivial let ?k=kernel let ?c=part2rel let ?i="Graph id"
let ?d=Domain let ?r=Range let ?G=Graph let ?g=graph let ?p=projector
let ?b="reducedbid i a" let ?B="quotientbid i a" let ?q=quotient
let ?Q="?q p ?B Id" let ?PP="?p (?b^-1) O ?Q" let ?P="?PP O ((?p Id)^-1)"
let ?PPP="(?p (?b^-1)) O (?p ?B)^-1 O p"
have "?Q=(?p ?B)^-1 O p O (?p Id)" using ll15 by blast
hence "?PP=(?p (?b^-1)) O (?p ?B)^-1 O p O (?p Id)" by presburger
hence "?P=?PPP O (?p Id) O ((?p Id)^-1)" by auto
also have "...=?PPP" using ll96 by (metis R_O_Id) ultimately have 
3: "?P=?PPP" by force moreover have 
0: "?r (?p (?b^-1))=?d ((?p ?B)^-1)" using ll12 quotientbid_def ll09
by (metis Domain_converse)
ultimately have "?r ((?p (?b^-1)) O (?p ?B)^-1) = ?r((?p ?B)^-1)" by blast
moreover have "... = ?d (?p ?B)" by auto
moreover have "... = ?d ?B" using ll09 by auto
moreover have "... = ?d ?b" using quotientbid_def ll09 by metis
moreover have "... = ?d a" using reducedbid_def ll09 by metis
ultimately have 
1: "?d (?p ?B)=?d a & ?d ?b=?d a & ?r ((?p (?b^-1)) O (?p ?B)^-1) \<subseteq> ?d p" 
using assms by presburger
hence "?d ?PPP=?d ((?p (?b^-1)) O (?p ?B)^-1)" by blast
also have "... = ?d (?p (?b^-1))" using 0 by blast
also have "... = ?d (?b^-1)" using ll13 by metis
also have "... = ?r ?b" by simp
have "b \<in> ?d ?b & ?u ?b" using assms 1 ll09 by simp then
moreover have "?b,,b \<in> ?r ?b" using ll14 by metis ultimately have 
2: "?b,,b \<in> ?d ?PPP" by simp have 
6: "b \<in> ?d(?p ?B) & ?d (?p ?B) \<subseteq> ?d p" using 1 assms by auto have 
4: "?u ?P" using ll02 by (metis assms(1) l15 ll87)
have "b \<in> ?d ?b" using ll09 assms by auto
moreover have "?u ?b" using l14 reducedbid_def by force
ultimately have "{?b,,b}=?b``{b}" using Image_runiq_eq_eval by metis
then have "?P``(?b``{b}) = ?P``{?b,,b}" by presburger
moreover have "... = {?P,,(?b,,b)}" using Image_runiq_eq_eval 2 3 4 by metis
have "b \<in> ?d p" using assms by fast then
moreover have "{p,,b}=p``{b}" using assms by (metis Image_runiq_eq_eval)
moreover have "... = ?P `` (?b``{b})" using ll07 assms 6 by blast
ultimately have "?P``(?b``{b})={?P,,(?b,,b)} & {p,,b}=?P``(?b``{b})" by force
then have "p,,b=?P,,(?b,,b)" by fastforce 
moreover have "?P=(?p (?b^-1)) O ?Q O ((?p Id)^-1)" by blast
ultimately show ?thesis by presburger
qed

definition reducedprice
(*MC: takes a triple (index domain, reduced bid, allocation) and yields a price 
(assuming quotientbid is compatible with p) *)
::"(bid \<times> price) set => index => (bid \<times> allocation ) set => ((index set \<times> bid \<times> allocation) \<times> price) set"
where "reducedprice p i a = 
((projector ((reducedbid i a)^-1)) O (quotient p (quotientbid i a) Id) O ((projector Id)^-1))"
(* MC: projector Id^-1 is the set-theoretical equivalent of the_elem, peeling
off the braces from a singleton: {x} \<longmapsto> x *)
(* Old def: "reducedprice p i a = ((reducedbid i a)^-1) O (Quotientbid i a) O 
(quotient p (quotientbid i a) (Graph id)) O (Graph the_elem)" *)

lemma ll06: fixes v::price fixes k::allocation 
fixes v1::"nat => price" fixes v2 i a p b 
assumes 
"cartesian a" 
"cartesian p"
"i \<in> Domain b" 
"b \<in> Domain a \<inter> (Domain p)" "dom4 i a p" "v1 ----> v" "v2 ----> v"
assumes "(%j . a,, (b +* {i}\<times>{v2 j}) - a,, (b +* {i}\<times>{v1 j})) ----> k" 
shows "(%j. (p,, (b +* {i}\<times>{v2 j}) - (p,, (b +* {i}\<times>{v1 j})))) ----> v*k"
proof -
(*Proof stub: weak dominance yields
\<forall>j . v1*[x(b2) - x(b1)] \<le> p(b2)-p(b1) \<le> v2*[x(b2) - x(b1)] 
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

definition weakefficient where "weakefficient a i b v a1 a2= 
(\<exists> v1 v2. (v1 ----> v) & (v2 ----> v) &
(%j . (a ,, (b +* ({i} \<times> {v1 j}) ))) = (%j . a1) &
(%j . (a ,, (b +* ({i} \<times> {v2 j}) ))) = (%j . a2))" 

lemma ll20: fixes a b i assumes "b \<in> Domain a" shows 
"reducedbid i a,,b=(Domain b, b outside {i}, a,,b)"
proof -
let ?d=Domain let ?f="%x. (?d x, x outside {i}, a,,x)"
let ?P="%x. x \<in> ?d a" let ?r="{(b, ?f b)| b. ?P b}"
have "?r,,b=?f b" using assms by (rule l16)
thus ?thesis using reducedbid_def by presburger
qed

lemma ll22: assumes 
"weakefficient a i b v a1 a2" 
"b \<in> Domain a" 
"cartesian a" 
"i \<in> Domain b" 
"runiq p"  
"Domain a \<subseteq> Domain p"
"runiq (quotient p (quotientbid i a) Id)"
"cartesian p" 
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
obtain v1 v2 where 
0: "(v1 ----> v) & (v2 ----> v) &
(%j . (a ,, (b +* {i}\<times>{v1 j}))) = (%j . a1) &
(%j . (a ,, (b +* {i}\<times>{v2 j}))) = (%j . a2)"
using assms weakefficient_def by metis
let ?b2="%j. b +* {i} \<times> {v2 j}"
let ?b1="%j. b +* {i} \<times> {v1 j}" have 
4: "\<forall>j. (a,,?b1 j=a1 & a,,?b2 j=a2)" using 0 by metis
have 
3: "b \<in> ?d a & cartesian a & i \<in> ?d b & ?u p & ?d a \<subseteq> ?d p
& ?u (?q p ?B Id)" using assms by blast
have "\<forall>j.(a,,(?b2 j)-(a,,(?b1 j))=?k)" using 4 by fast
have "((%j. (a,, (?b2 j) - a,, (?b1 j)))) ----> ?k"
using tendsto_const 4 by auto
also have "cartesian p & dom4 i a p" 
(*  "i \<in> ?d b" "v1 ----> v" "v2 ----> v" "b \<in> ?d a \<inter> (?d p)"*)
using assms by fast
ultimately have 
1: "(%j. (p,, (?b2 j) - (p,, (?b1 j)))) ----> v*?k"
using 3 ll06 assms 0 by blast
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
"i \<in> Domain b" "b \<in> Domain a" "cartesian a" "cartesian p" "runiq p"  
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

corollary (*MC: MASKIN's theorem 2 as a corollary of ll24 and ll08 *)
(*MC: In the canonical (Maskin's paper) case, i=argmax b, 
a=delta (j,i), a1=0 and a2=1; this particular case of course happens to satisfy
weakefficient request below upon setting v=max (b outside {i}), and expresses 
the property that "the high bidder must win" (quoting Maskin's paper).
dom4 is weak dominance *)
assumes
"weakefficient a i b v a1 a2" 
"i \<in> Domain b" "b \<in> Domain a" "cartesian a" "cartesian p" "runiq p"  
"Domain a \<subseteq> Domain p" "dom4 i a p" "functional (Domain a)"
shows
"a,,b=a1 \<longrightarrow> p,,b=reducedprice p i a,,(Domain b, b outside {i}, a1) & 
a,,b=a2 \<longrightarrow> p,,b = v*(a2-a1) + (reducedprice p i a ,, (Domain b, b outside {i}, a1))"
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
ultimately have "a,,b=a1 \<longrightarrow> p,,b=?P,,(?I, ?bb, a1)" by presburger
have "?P,,(?I, ?bb, a2)=v*(a2 - a1) + ?P,,(?I,?bb, a1)" using assms ll24 by blast
then moreover have "a,,b=a2 \<longrightarrow> p,,b=v*(a2 - a1) + ?P,,(?I,?bb, a1)" using 0 by (metis (full_types) `reducedprice p i a ,, (reducedbid i a ,, b) = reducedprice p i a ,, (Domain b, b outside {i}, a ,, b)`)
finally show ?thesis by fastforce
qed

(* bigskip

definition weakefficientOld where "weakefficientOld a i = 
(\<forall> b::bid . \<exists> v v1 v2 a1 a2. 
(v1 ----> v) &
(v2 ----> v) &
(%j . (a ,, (b +* {(i, v1 j)}))) = (%j . a1) &
(%j . (a ,, (b +* {(i, v2 j)}))) = (%j . a2) &
(a1 \<noteq> a2)
)" 














lemma assumes "weakdom i a p" shows "weakdomgen (%X. card X=1) i a p"
using weakdom_def weakdomgen_def sorry

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
(?f Y (?aa,, b))-(p,, b) \<le> (?f Y (?aa,, (b+* ({i}\<times>Y)))) - (p,, (b+* ({i}\<times>Y))))" sorry 
then
have "?P ?f" by fast then
have "EX f. (?P f)" by fastforce
hence "dom2 i ?aa p" using dom2_def by presburger
thus ?thesis by simp
qed

(*
theorem ll58: fixes i a p b  assumes "b \<in> Domain p" "runiq p" "weakdom i a p"
shows "p ,, b = (reducedprice p i a) ,, (reducedbid i a ,, b)"
proof -
let ?D="Domain" let ?G="Graph" let ?I="?G id" let ?r="reducedbid i a" let ?e="the_elem"
let ?B="?r,, b" let ?q="quotientbid i a" let ?Q="Quotientbid i a"  let ?E="?G ?e"
let ?f="quotient p ?q ?I" let ?F="(?r^-1) O ?Q O ?f O ?E" have
0:"runiq ?f & runiq ?E" sorry
have "((?r^-1) O ?Q),, ?B = ?q`` {b}" sorry
hence "?F,, ?B = (?f O ?E),, (?q`` {b})" using eval_rel_def sorry
also have "... = ?E,, (?f,, (?q``{b}))" using 0 eval_rel_def sorry
finally have "True" sorry
have "b \<in> ?q ``{b} & (b, p,,b) \<in> p" sorry then
have "(?q``{b} \<times> {p,, b}) \<inter> p \<noteq> {}" by fast
have "(?q``{b}, {p,, b}) \<in> ?f" using quotient_def assms sorry
have "runiq ?Q" by (metis Quotientbid_def l15) 
have "b \<in> ?D ?q" sorry
then have 
"?Q,, b=?q``{b}" using Quotientbid_def l17 by metis 
show ?thesis sorry
qed
(* the point is that reducedprice p i a depends on a pair 
(b outside {i}, a ,, b) , given by reducedbid i a ,, b ;
hence it no longer depends on the whole bid vector b *)
*)

bigskip *)

end

