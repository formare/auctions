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

theory d1

imports "../Maskin2" (* SupInf SEQ*) Limits 

begin

type_synonym price = real
type_synonym participant = nat
type_synonym good = nat
(*
type_synonym allocation = real
type_synonym bid = "(participant \<times> price) set"
*)
(*
definition prices where "prices = \<real>"
definition allocations where "allocations = \<real>"
*)
definition indices where "indices = \<nat>"

type_synonym allocation = "good => participant"
type_synonym valuation = "allocation => price"
type_synonym bid = "(participant \<times> valuation) set"


(* MC: have to investigate what entities we require 
the currency and the allocation values to be represented by.
Rational and Reals will do, but I guess sub{rings,fields} of a field with 
some order and topology will be sufficient to prove Maskin2. 
Mathematically, this is probably the most interesting issue;
not sure whether there is enough Isabelle library
to tackle that, so for the moment let's stick to \<rat>, \<real>. *)

definition weakdom
(* ::"participant => (bid \<times> allocation) set => (bid \<times> price) set => bool" *)
where "weakdom i a p \<eta> = 
( \<forall> b::bid .\<forall> Y. 
(Y \<noteq> {} & {b, b+*({i}\<times>Y)} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b) \<longrightarrow> 
((\<eta>(b,Y) (a,, b))-(p,, b) \<le> \<eta>(b,Y) (a,, (b+* ({i}\<times>Y))) - (p,, (b+* ({i}\<times>Y)))
))"
(*MC: Later, we will require a or p to be defined only on runiq bids, 
so that R must be a singleton and we can use r=the_elem R *)
(* MC: The problem here is the multiplication of a price (r) 
and an allocation. 
They should be allowed to be of different subtypes (e.g., real and nat) of 
a supertype admitting multiplication, order and subtraction.
In Mizar, the clustering+type widening mechanism makes such things painless.
What about Isabelle? *)

definition dom4 where "dom4 i a p = (
\<forall> b::bid. \<forall> v. ({b, b+* ({i}\<times>{v})} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b) \<longrightarrow>
v*(a,,b)-(p,,b) \<le> v*(a,,(b+*({i}\<times>{v})))-(p,,(b+*({i}\<times>{v}))))"

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

definition reducedbid 
:: "participant => (bid \<times> allocation) set => 
(bid \<times> participant set \<times> bid \<times> allocation) set"
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
  (* have "?d a \<subseteq> ?d p & ?w & ?u p" using assms by fast
  then have "?c p ?p ?Id" using l24 by auto *)
  have "?u ?b" using l14 reducedbid_def by force then
  have "equiv (?d ?p) ?p" using ll78 assms by (metis l47 ll80)
  moreover have "?Id=Id & equiv (?d Id) Id" using ll95 equiv_def Domain_Id refl_Id sym_Id trans_Id
  by metis
  moreover have "?c p ?p ?Id" using l24 assms by blast
  ultimately show "?u (?q p ?p Id)" using l23 equiv_def assms by metis
qed

definition quotientbid where "quotientbid i a = part2rel (kernel (reducedbid i a))"

definition Quotientbid where "Quotientbid i a = projector (quotientbid i a)"

corollary ll09: fixes i a shows "Domain (reducedbid i a) = Domain a 
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

corollary ll15: shows "quotient p (quotientbid i a) Id = 
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
  also have "equiv (?d Id) Id" using equiv_def 
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
(* the point is that reducedprice p i a depends on a pair 
(b outside {i}, a ,, b) , given by reducedbid i a ,, b ;
hence it no longer depends on the whole bid vector b *)
assumes "runiq (quotient p (quotientbid i a) Id)" "runiq p" "b \<in> Domain a" "Domain a \<subseteq> Domain p"
shows "p,,b = 
((projector ((reducedbid i a)^-1)) O (quotient p (quotientbid i a) Id) O ((projector Id)^-1))
,, (reducedbid i a,,b)"
proof -
  (* TODO@MC: modularize&clean *)
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
  0: "?r (?p (?b^-1))=?d ((?p ?B)^-1)" using ll12 quotientbid_def ll09 by (metis Domain_converse)
  ultimately have "?r ((?p (?b^-1)) O (?p ?B)^-1) = ?r((?p ?B)^-1)" by blast
  moreover have "... = ?d (?p ?B)" by auto moreover have "... = ?d ?B" using ll09 by auto
  moreover have "... = ?d ?b" using quotientbid_def ll09 by metis
  moreover have "... = ?d a" using reducedbid_def ll09 by metis
  ultimately have 
  1: "?d (?p ?B)=?d a & ?d ?b=?d a & ?r ((?p (?b^-1)) O (?p ?B)^-1) \<subseteq> ?d p" 
  using assms by presburger hence "?d ?PPP=?d ((?p (?b^-1)) O (?p ?B)^-1)" by blast
  also have "... = ?d (?p (?b^-1))" using 0 by blast
  also have "... = ?d (?b^-1)" using ll13 by metis also have "... = ?r ?b" by simp
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
(*MC: takes a triple (participant domain, reduced bid, allocation) and yields a price 
(assuming quotientbid is compatible with p) *)
::"(bid \<times> price) set => participant => (bid \<times> allocation ) set => ((participant set \<times> bid \<times> allocation) \<times> price) set"
where "reducedprice p i a = 
((projector ((reducedbid i a)^-1)) O (quotient p (quotientbid i a) Id) O ((projector Id)^-1))"
(* MC: projector Id^-1 is the set-theoretical equivalent of the_elem, peeling
off the braces from a singleton: {x} \<longmapsto> x *)
(* Old def: "reducedprice p i a = ((reducedbid i a)^-1) O (Quotientbid i a) O 
(quotient p (quotientbid i a) (Graph id)) O (Graph the_elem)" *)

definition dom1 
(* ::"_ => _ => _ => valuation => _" *)
where "dom1 i a p v = 
(\<forall> b. v (a,,b) - p,,b \<le> v (a,,(b+*({i}\<times>{v}))) - p,,(b+*({i}\<times>{v})))"

(*
definition dom0
(* ::"participant => (bid \<times> allocation) set => (bid \<times> price) set => bool" *)
where "dom0 i a p = 
( \<forall> b::bid .\<forall> y. 
({b, b+*({i}\<times>{y})} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b) \<longrightarrow> 
(EX v.(v (a,, b))-(p,, b) \<le> v (a,, (b+* ({i}\<times>{y}))) - (p,, (b+* ({i}\<times>{y})))
))"

lemma assumes "dom0 i a p" "functional (Domain a \<inter> (Domain p))" 
shows "weakdom i a p"
proof -
  let ?d=Domain let ?w=weakdom let ?I="{i}" let ?t=trivial let ?u=runiq
  {
    fix b fix Y::"valuation set" let ?y="the_elem Y" let ?s="?I \<times> Y" let ?bi="b +* ?s"
    assume 
    0: "Y \<noteq> {} & {b, ?bi} \<subseteq> (?d a \<inter> (?d p)) & i \<in> ?d b"
    then have "?u ?bi" using assms functional_def by blast
    moreover have "Y = ?s``?I & ?d ?s=?I" using 0 by fast
    then moreover have "?s``?I = ?bi `` ?I" using assms ll50 by (metis Int_absorb)
    ultimately have "?t Y" by (metis runiq_alt)
    hence 
    2: "Y={?y}" using 0 by (metis subset_singletonD trivial_def)
    then obtain y where 
    1: "(y (a,, b))-(p,, b) \<le> y (a,, (b+* ({i}\<times>{?y}))) - (p,, (b+* ({i}\<times>{?y})))"
    using assms 0 dom0_def by metis
    have "EX y.(y (a,, b))-(p,, b) \<le> y (a,, (b+* ({i}\<times>Y))) - (p,, (b+* ({i}\<times>Y)))"
    using 1 2 by fastforce
  }
  then have "?w i a p" using weakdom_def by metis
  thus ?thesis by fast
qed

lemma assumes "! v.(dom1 i a p v)" shows "dom0 i a p"
proof -
  let ?d=Domain let ?r=Range
  {
    fix b fix y::valuation let ?s="{i}\<times>{y}" let ?bi="b +* ?s" 
    assume "{b,?bi} \<subseteq> (?d a \<inter> (?d p)) & i \<in> ?d b"
    have "(y (a,, b))-(p,, b) \<le> y (a,, (b+* ({i}\<times>{y}))) - (p,, (b+* ({i}\<times>{y})))"
    using assms dom1_def by fast
    then have "EX v. (v (a,, b))-(p,, b) \<le> v (a,, (b+* ({i}\<times>{y}))) - (p,, (b+* ({i}\<times>{y})))"
    by blast
  }
  thus ?thesis using dom0_def by blast
qed 
 
definition dom2 where "dom2 i a p = 
(EX f::(price set => allocation => price). \<forall> b::bid. \<forall> Y. ({b, b+*({i}\<times>Y)} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b
\<longrightarrow>
(f Y (a,, b))-(p,, b) \<le> (f Y (a,, (b+* ({i}\<times>Y)))) - (p,, (b+* ({i}\<times>Y)))))"
(* Stronger than above: we require that the function to obtain y 
is independent of b and Y *)

definition dom3 where "dom3 i a p = (
\<forall> b::bid. \<forall> Y. {b, b +* ({i} \<times> Y)} \<subseteq> (Domain a \<inter> (Domain p)) & i \<in> Domain b \<longrightarrow>(
the_elem Y*(a,, b) - (p,, b)) \<le> 
the_elem Y*(a,, (b+* ({i} \<times> Y))) - (p,, (b+* ({i}\<times>Y))))"
*)

end

