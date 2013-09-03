theory b

imports a RelationProperties Maximum

begin

lemma ll23: fixes X Y assumes "trivial Y" assumes "X \<subseteq> Y" 
shows "trivial X"
proof -
show ?thesis using assms trivial_def by (metis (hide_lams, no_types) all_not_in_conv set_mp subsetI subset_singletonD)
qed

lemma ll24: fixes f R::"('a \<times> 'b) set" assumes "runiq f" assumes "R \<subseteq> f"
shows "runiq R"
proof -
{
  fix X::"'a set" assume "trivial X"
  hence "trivial (f `` X) & (R `` X \<subseteq> (f `` X))" 
  using assms runiq_def by blast
  hence "trivial (R `` X)" using ll23 by metis
}
thus ?thesis using runiq_def by auto
qed

lemma ll22: assumes "finite X" shows "length (sorted_list_of_set X) = card X"
proof - show ?thesis using assms by (metis distinct_card sorted_list_of_set) qed

lemma ll10: "P = (P outside X) \<union> (P || X)"
proof -
show ?thesis using assms Outside_def restrict_def by (metis Un_Diff_Int inf_commute)
qed

lemma ll09: assumes "P || (Domain Q) \<subseteq> Q" shows "P +* Q = P \<union> Q"
proof -
show ?thesis using assms paste_def ll10 by (smt Un_commute Un_left_commute le_sup_iff subset_antisym subset_refl sup_ge2)
qed

lemma ll12: "P || {} = {}"
proof -
show ?thesis using restrict_def by (metis Int_empty_left Sigma_empty1)
qed

lemma ll26: "P || X \<subseteq> P"
proof -
show ?thesis using restrict_def by blast
qed

lemma ll11: "P || X = P || (X \<inter> (Domain P))" 
proof -
let ?D="Domain P" let ?LH="P || X" let ?RH="P || (X \<inter> ?D)" let ?R="Range P"
(*have "?LH \<supseteq> ?RH" using restrict_def Domain_def ll26 
by (smt Int_lower1 Sigma_Int_distrib1 inf_mono order_refl)*)
have "P = P \<inter> (?D \<times> ?R)" by fast
hence "?LH = (P \<inter> (?D \<times> ?R)) \<inter> (X \<times> ?R)" using restrict_def by auto
also have "... = P \<inter> ((?D \<times> ?R) \<inter> (X \<times> ?R))" by blast
also have "... = P \<inter> ((?D \<inter> X) \<times> ?R)" by fast
also have "... = P || (X \<inter> ?D)" using restrict_def by fastforce
ultimately show "?LH = ?RH" by presburger
qed

lemma ll13: assumes "Domain P \<inter> (Domain Q)={}" shows "P +* Q = P \<union> Q"
proof -
show ?thesis using ll09 ll11 ll12 assms by (metis inf.commute inf_sup_ord(3) sup_bot_left)
qed

lemma ll07: fixes X Y f F assumes "F = (%Z . ({ f z | z. z \<in> Z}))" 
shows "F (X \<union> Y) = F X \<union> (F Y)"
proof - (* pattern matching would be good here *)
let ?F="%Z . ({ f z | z. z \<in> Z})" let ?XY="X \<union> Y"
let ?LH="?F ?XY" let ?XX="?F X" let ?YY="?F Y" let ?RH="?XX \<union> ?YY"
have "?LH \<subseteq> ?RH" by fast also have "?RH \<subseteq> ?LH" by fast
ultimately show ?thesis using assms by fast
qed

lemma ll06: "inverse R = { (snd z, fst z) | z. z\<in>R }"
proof -
show ?thesis using inverse_def sorry
qed

lemma ll08: fixes P Q shows "inverse (P \<union> Q)=inverse P \<union> (inverse Q)"
proof -
(* let ?IP="inverse P" let ?IQ="inverse Q" let ?R="P \<union> Q" let ?LH="inverse ?R"
let ?RH="?IP \<union> ?IQ" *)
show ?thesis using inverse_def assms ll07 ll06 sorry
qed

lemma ll25: fixes P Q assumes "P \<subseteq> Q" shows "inverse P \<subseteq> inverse Q"
proof -
show ?thesis using assms by (metis ll08 subset_Un_eq)
qed

lemma ll01: fixes P Q assumes "runiq Q" assumes "runiq (P outside (Domain Q))" 
shows "runiq (P +* Q)"
proof - 
show ?thesis using assms runiq_def paste_def Outside_def sorry
qed

lemma ll02: fixes x X assumes "trivial X" assumes "x \<subseteq> X" shows "trivial x"
proof -
show ?thesis using assms trivial_def by (metis (hide_lams, no_types) all_not_in_conv set_mp subsetI subset_singletonD)
qed

lemma ll03: fixes P Q::"('a \<times> 'b) set" assumes "P \<subseteq> Q & runiq Q" shows "runiq P"
proof -
{
  fix X::"'a set" assume "trivial X" 
  hence "X \<subseteq> X & trivial (Q `` X)" using assms runiq_def by fast
  hence "trivial (P `` X)" using assms Image_mono ll02 by metis
}
thus ?thesis using runiq_def Image_mono by blast
qed

corollary ll04: fixes P Q assumes "runiq Q" assumes "runiq P" 
shows "runiq (P +* Q)"
proof -
show ?thesis using ll01 ll03 Outside_def by (metis Diff_subset assms(1) assms(2))
qed

lemma ll05: shows "runiq {(x,y)}"
proof -
let ?f="%x . y" let ?P="% xx. xx=x" let ?X1="{(x,y)}" 
let ?X2="{(xx, ?f x) | xx. ?P xx}"
have "?X1 = ?X2" by auto also have "runiq ?X2" using l14 by fast
ultimately show ?thesis by presburger
qed

lemma assumes "trivial X" shows "runiq X"
proof -
show ?thesis using ll05 trivial_def by (metis assms ll03 surj_pair)
qed

lemma ll28: shows "P=(P outside X) +* (P || X)"
proof -
let ?p="P outside X" let ?q="P || X" let ?dp="Domain ?p" let ?dq="Domain ?q"
let ?D="Domain P" have "P \<subseteq> ?D \<times> (Range P)" by fast
hence "?p \<subseteq> ?D \<times> (Range P) - (X \<times> (Range P))" using Outside_def by (metis Diff_mono eq_refl)
hence "?dp \<subseteq> ?D - X" using Outside_def Domain_def by blast
also have "?dq=?D \<inter> X" using restrict_def by fastforce
ultimately have "?dp \<inter> ?dq = {}" by blast thus ?thesis using ll10 ll13 by metis
qed


definition childrenof 
(*::" ('a \<times> 'b::linorder) set => 'a => ('b set) => ('a \<times> 'b) set list"*)
where 
"childrenof R x Y = [ R +* {(x,y)} . y <- (sorted_list_of_set (Y - Range R))]"
(* Y or Y-Range R ? *)

fun bijections 
(*::"'a list => 'b::linorder set => ('a \<times> 'b) set list"*)
where
"bijections [] Y = [{}]" |
"bijections (x # xs) Y = concat [ childrenof R x Y . R <- bijections xs Y ]"

lemma ll27: shows "set (concat LL)= \<Union> {set l | l . l \<in> set LL}"
proof -
show ?thesis sorry
qed

definition F
::"'a => ('b::linorder set) => nat => ('a::linorder \<times> 'b) set set"
where 
"F x Y n = \<Union> {set (bijections l Y) | l . size l=n & card (set l)=n}"

definition G
::"'a => ('b::linorder set) => nat => ('a::linorder \<times> 'b) set set"
where 
"G x Y n = {f . 
finite (Domain f) & card (Domain f)=n & runiq f & runiq (inverse f) & Range f \<subseteq> Y}"

notepad
begin
fix Y n
let ?l="sorted_list_of_set" let ?B="bijections"
let ?F="%n. (\<Union> {set (bijections l Y) | l . size l=n & card (set l)=n})"
let ?G="%n. {f . finite (Domain f) & card (Domain f)=n & runiq f & runiq (inverse f) & Range f \<subseteq> Y}"
let ?Fn="?F n" let ?Gn="?G n"
have "?B (?l {}) Y = [{}]" using bijections_def by auto
hence "?F 0 = {{}}" by auto
have "\<forall> f . (finite (Domain f) & card (Domain f)=0 \<longrightarrow> f={})" by (metis Domain_empty_iff card_eq_0_iff)
hence "\<forall> f. (f \<in> ?G 0 \<longrightarrow> f={})" by fast
hence 0: "?G 0 \<subseteq> {{}}" by blast
have 1: "finite (Domain {})" by simp
have 2: "card (Domain {})=0" by force
have 3: "runiq {}" using runiq_def trivial_def by fast
also have "inverse {} = {}" using inverse_def ll06 by fast
ultimately have "runiq (inverse {})" by metis
hence "{} \<in> ?G 0" using 1 2 3 by blast
hence "?G 0 = {{}}" using 0 by auto
end

lemma ll16: fixes l Y R assumes "R \<in> set (bijections l Y)" shows "Domain R = set l"
proof -
show ?thesis sorry
qed

definition isbij where "isbij f = (runiq f & runiq (inverse f))"

lemma ll14: fixes f x assumes "runiq f" assumes "x \<notin> Domain f" 
shows "runiq (f +* {(x,y)})"
proof - show ?thesis using assms ll04 ll05 by metis qed

lemma ll15: fixes f x Y assumes "runiq (inverse f)" assumes "y \<in> (Y - Range f)" 
assumes "x \<notin> Domain f" (* this lemma should be split or generalized *)
shows "runiq (inverse (f +* {(x,y)}))"
proof -
have
1: "Domain f \<inter> Domain {(x,y)}={}" using assms by fast
have "y \<notin> Range f" using assms by fast 
also have "Range f = Domain (inverse f)" (* ... notation here would be nice *)
using inverse_def Domain_def Range_def by blast 
ultimately have 2: "Domain (inverse f) \<inter> Domain {(y,x)}={}" by force
have "inverse {(x,y)}={(y,x)}" using ll06 ll07 by auto
then have "inverse (f \<union> {(x,y)}) = inverse f \<union> {(y,x)}" using ll08 by blast
also have "... = inverse f +* {(y,x)}" using 2 ll13 by metis
also have "runiq (inverse f +* {(y,x)})" using ll04 ll05 assms by metis
ultimately have "runiq (inverse (f \<union> {(x,y)}))" by presburger
also have "f +* {(x,y)} = f \<union> {(x,y)}" using 1 ll13 by metis
ultimately show "runiq (inverse (f +* {(x,y)}))" by presburger
qed

lemma ll17: shows "Domain (P \<union> Q) = Domain P \<union> (Domain Q)"
proof -
show ?thesis by (metis Domain_Un_eq)
qed

lemma ll19: shows "Domain (P outside X)= Domain P - X"
proof -
show ?thesis using Outside_def by blast
qed

lemma ll20: shows "Domain (P +* Q) = (Domain P \<union> Domain Q)"
proof -
show ?thesis using ll17 ll19 paste_def by (metis Un_Diff_cancel Un_commute)
qed

lemma ll18: shows "P +* Q \<subseteq> P \<union> Q"
proof -
have "P outside (Domain Q) \<subseteq> P" using Outside_def by blast
also have "Q \<subseteq> Q" by fast
ultimately show ?thesis using paste_def by (metis (hide_lams, no_types) le_supI1 le_sup_iff sup_commute)
qed

lemma ll21: shows "Range (P +* Q) \<subseteq> Range P \<union> (Range Q)"
proof -
show ?thesis using ll18 by (metis Range_Un_eq Range_mono)
qed

lemma ll29: shows "P || {x} = {x} \<times> (P `` {x})"
proof -
show ?thesis sorry
qed

lemma ll30: fixes x f assumes "x \<in> Domain f" assumes "runiq f" 
shows "f `` {x} = {f ,, x}"
proof -
let ?X="{x}" let ?Y="f `` ?X" let ?y="f ,, x"
have "?Y \<subseteq> {?y}" using assms l2 by metis
also have "?y \<in> ?Y" using assms l25 by (metis Image_singleton_iff)
ultimately show ?thesis by blast
qed

lemma ll31: fixes X1 X2 R assumes "R `` X1 \<inter> (R `` X2) = {}" 
shows "Domain R \<inter> X1 \<inter> X2={}"
proof -
let ?Y1="R `` X1" let ?Y2="R `` X2" let ?D="Domain R" let ?X="X1 \<inter> X2"
have "R `` (?D \<inter> ?X) = R `` ?X" by fast also have "R `` ?X \<subseteq> ?Y1 \<inter> ?Y2" by blast
ultimately have 
1: "R `` (?D \<inter> ?X) \<subseteq> ?Y1 \<inter> ?Y2" by simp
{
  fix x assume 
  0: "x \<in> ?D \<inter> ?X" 
  hence "R `` {x} \<subseteq> R `` (?D \<inter> ?X)" by blast
  also have "R `` {x} \<noteq> {}" using 0 by fast
  ultimately have "?Y1 \<inter> ?Y2 \<noteq> {}" using 1 by force
}
thus ?thesis using assms Image_def by fast
qed

lemma ll32: assumes "runiq f" assumes "runiq (inverse f)"
shows "inverse f O f \<subseteq> Graph id"
proof -
show ?thesis using assms sorry
qed

lemma fixes X1 X2 f assumes "Domain f \<inter> X1 \<inter> X2 = {}" 
assumes "runiq f" assumes "runiq (inverse f)"
shows "f `` X1 \<inter> (f `` X2)={}"
proof -
let ?g="inverse f" let ?Y1="f `` X1" let ?Y2="f `` X2" let ?D="Domain f"
let ?XX1="?D \<inter> X1" let ?XX2="?D \<inter> X2" have 
1: "g `` (f `` ?XX1) \<subseteq> ?XX1" using ll32 assms sorry have 
2: "g `` (f `` ?XX2) \<subseteq> ?XX2" using ll32 assms sorry 
hence 
4: "g `` (f `` ?XX1) \<inter> (g `` (f `` ?XX2)) \<subseteq> {}" using assms 1 by blast
have 
3: "?XX1 \<inter> ?XX2 = {}" using assms by blast
hence "{} = Domain g \<inter> (f `` ?XX1) \<inter> (f `` ?XX2)" using ll31 4 by fast
also have "... = Range f \<inter> (f `` ?XX1) \<inter> (f `` ?XX2)" sorry
also have "... = f `` ?XX1 \<inter> (f `` ?XX2)" by blast
show ?thesis sorry
qed

























lemma fixes x Y n assumes "G x Y n \<subseteq> F x Y n" shows "G x Y (Suc n) \<subseteq> F x Y (Suc n)"
proof -
let ?B="bijections" let ?l="sorted_list_of_set" let ?c="childrenof"
let ?N="Suc n" let ?F="F x Y" let ?G="G x Y" 
let ?Fn="?F n" let ?Gn="?G n" let ?FN="?F ?N" let ?GN="?G ?N"
{
fix g
(* ::"('a::linorder \<times> 'b::linorder) set" *) 
assume
0: "g \<in> G x Y (Suc n)"
let ?DN="Domain g" let ?lN="?l ?DN" let ?x="hd ?lN" let ?ln="drop 1 ?lN" 
let ?f="g outside {?x}" let ?y="g ,, ?x" let ?RN="Range g" let ?Dn="Domain ?f" 
let ?Rn="Range ?f" let ?e="% z . (?f +* {(?x,z)})" have 
6: "finite ?DN & card ?DN=?N & runiq g & runiq (inverse g) & ?RN \<subseteq> Y" 
using 0 G_def by blast
hence "set ?lN=?DN" using sorted_list_of_set_def by simp
also have "?lN \<noteq> []" using 6 
by (metis Zero_not_Suc `set (sorted_list_of_set (Domain g)) = Domain g` card_empty empty_set)
ultimately have 
7: "?x \<in> ?DN" using 0 hd_in_set by metis
have "g = ?f +* ({?x} \<times> g `` {?x})" using ll28 ll29 by metis
also have "... = ?f +* ({?x} \<times> {?y})" using 6 7 ll30 by metis
also have "... = ?f +* {(?x, ?y)}" by simp
ultimately have "g = ?e ?y" by presburger
also have "?y \<in> set (?l (Y - Range ?f))" sorry
ultimately have "g \<in> set [?e z . z <- ?l (Y - Range ?f)]" by auto hence 
2: "g \<in> set (childrenof ?f ?x Y)" using childrenof_def by metis have 
22: "?f \<subseteq> g" using Outside_def by (metis Diff_subset)
hence "inverse ?f \<subseteq> inverse g" using ll25 by metis
have
21: "card ?DN=?N & runiq g & runiq (inverse g) & ?RN \<subseteq> Y" using 0 G_def by blast hence 
23: "finite ?DN" using card_ge_0_finite by force hence 
24: "finite ?Dn" by (metis finite_Diff ll19) have 
25: "runiq ?f" using ll24 Outside_def 21 by (metis Diff_subset) have 
26: "runiq (inverse ?f)" using ll24 22 ll25 21 by metis have 
27: "?Dn = ?DN - {?x}" by (metis ll19)
have "?x \<in> ?DN" using 23 sorted_list_of_set by (metis "21" Diff_empty Suc_diff_le Suc_eq_plus1_left add_diff_cancel_right' card_Diff_subset diff_le_self empty_set hd_in_set le_bot not_less_bot not_less_eq order_refl)
hence "card ?Dn=card ?DN - 1" using 27 card_Diff_singleton 23 by metis
hence "card ?Dn = n & ?Rn \<subseteq> ?RN" using 21 22 by auto
hence "card ?Dn = n & ?Rn \<subseteq> Y" using 21 by fast
hence "?f \<in> G x Y n" using 24 25 26 21 G_def by blast
hence "?f \<in> F x Y n" using assms by fast
then obtain ln::"'a list" where
1: "?f \<in> set (?B ln Y) & size ln=n & card (set ln)=n" using F_def by blast
let ?lN="?x # ln" have 
3: "size ?lN=?N" using 1 by (metis Suc_length_conv) 
have "g \<in> set (concat [ ?c R ?x Y . R <- ?B ln Y])" using 1 2 by auto hence 
4: "g \<in> set (?B (?x # ln) Y)" using bijections_def by auto
hence "card (set ?lN)=?N" using 1 by (metis "21" ll16)
hence "g\<in>?FN" using F_def 3 4 by blast
also have "size ?lN=?N & card (set ?lN)=?N" 
using 6 7 by (metis "3" `card (set (hd (sorted_list_of_set (Domain g)) # ln)) = Suc n`)
ultimately have "g \<in> ?FN" using F_def by blast
}
thus "?GN \<subseteq> ?FN" by force
qed

lemma 
fixes x::"'a::linorder" 
fixes Y::"'b::linorder set"
fixes n::nat
assumes "finite Y"
assumes "F x Y n \<subseteq> G x Y n" shows "F x Y (Suc n) \<subseteq>
 G x Y (Suc n)"
proof -
let ?r="%x . runiq x" let ?F="F x Y" let ?G="G x Y" let ?B="bijections"
let ?c="childrenof" let ?l="sorted_list_of_set"
let ?Fn="?F n" let ?N="Suc n" let ?FN="?F ?N" let ?Gn="?G n" let ?GN="?G ?N"
{ 
  fix g assume "g \<in> F x Y (Suc n)" then 
  have "g \<in> \<Union> {set (?B l Y) | l . size l=(Suc n) & card (set l)=(Suc n)}" 
  using F_def by (metis (mono_tags))
  then obtain a::"('a \<times> 'b) set set" where 
  0: "g\<in> a & a\<in> {set (?B l Y) | l . size l=?N & card (set l)=?N}" 
  using F_def by blast
  obtain lN where
  1: "a=set (?B lN Y) & size lN=?N & card (set lN)=?N" using 0 by blast  
  let ?DN="set lN" 
  let ?x="hd lN" let ?ln="drop 1 lN" have
  2: "lN=?x # ?ln & size ?ln=n & card (set ?ln)=n & set ?ln=set lN-{?x}" sorry 
  have "?B (?x # ?ln) Y=concat [ ?c R ?x Y . R <- bijections ?ln Y]" 
  using bijections_def by auto
  hence "set (?B lN Y) = \<Union> {set l | l . l \<in> set [ ?c R ?x Y. R <- bijections ?ln Y]}"
  using ll27 2 by metis 
  then obtain f where 
  3: "f \<in> set (?B ?ln Y) & g \<in> set (?c f ?x Y)" using bijections_def 0 1 by auto
  let ?if="inverse f"
  have "set (?B ?ln Y) \<in> {set (bijections l Y) | l . size l=n & card (set l)=n}"
  using 2 by blast 
  hence "f \<in> ?Fn" using 2 3 F_def by fast
  hence "f \<in> ?Gn" using assms by blast hence 
  5: "finite (Domain f) & card (Domain f)=n & runiq f & runiq ?if & Range f \<subseteq> Y"
  using G_def by blast
  have "g \<in> set [ f +* {(?x,y)} . y <- ?l (Y - Range f) ]" using 3 childrenof_def by metis
  then obtain y where
  4: "g=f +* {(?x, y)} & y \<in> set (?l (Y - Range f))" using 3 childrenof_def by auto
  have "finite (Y -Range f)" using assms by fast hence
  6: "g=f +* {(?x, y)} & y \<in> Y - Range f" 
  using 4 sorted_list_of_set by metis hence 
  9: "runiq g" using ll04 5 ll05 by fast
  have "Domain f=set ?ln" using ll16 3 by blast hence 
  7: "?x \<notin> Domain f & card (Domain f)=n" using 2 by force hence 
  8: "runiq (inverse g)" using ll15 5 6 by metis have 
  10: "Range g \<subseteq> Range f \<union> {y}" using 6 by (metis Range_empty Range_insert ll21)
  (* simplify this using g=f \<union> {...} *)
  have "Domain g=Domain f \<union> {?x}" using 6 ll20 by (metis Domain_empty Domain_insert)
  hence "card (Domain g)=?N" using 7 5 by auto
  hence "card (Domain g)=?N & finite (Domain g)" using card_ge_0_finite by force
  hence "g \<in> ?GN" using G_def 8 9 10 5 6 by fast
}
thus ?thesis by fast
qed

lemma fixes x Y n assumes "G x Y n \<subseteq> F x Y n" shows "G x Y (Suc n) \<subseteq> F x Y (Suc n)"
proof -
let ?B="bijections" let ?l="sorted_list_of_set" let ?c="childrenof"
let ?N="Suc n" let ?F="F x Y" let ?G="G x Y" 
let ?Fn="?F n" let ?Gn="?G n" let ?FN="?F ?N" let ?GN="?G ?N"
{
fix g
(* ::"('a::linorder \<times> 'b::linorder) set" *) 
assume
0: "g \<in> ?G (Suc n)"
let ?DN="Domain g" 
let ?lN="sorted_list_of_set ?DN" 
let ?x="hd ?lN" let ?ln="drop 1 ?lN" let ?f="g outside {?x}"
let ?y="g ,, ?x" 
let ?RN="Range g"
let ?Dn="Domain ?f" let ?Rn="Range ?f"
have "g = ?f \<union> ({?x} \<times> g `` {?x})" sorry
also have "... = ?f +* {(?x, ?y)}" sorry
hence 
2: "g \<in> set (childrenof ?f ?x Y)" using childrenof_def sorry
have 
22: "?f \<subseteq> g" using Outside_def by (metis Diff_subset)
hence "inverse ?f \<subseteq> inverse g" using ll25 by metis
have
21: "card ?DN=?N & runiq g & runiq (inverse g) & ?RN \<subseteq> Y" using 0 G_def by blast hence 
23: "finite ?DN" using card_ge_0_finite by force hence 
24: "finite ?Dn" by (metis finite_Diff ll19) have 
25: "runiq ?f" using ll24 Outside_def 21 by (metis Diff_subset) have 
26: "runiq (inverse ?f)" using ll24 22 ll25 21 by metis
have 
27: "?Dn = ?DN - {?x}" by (metis ll19)
have "?x \<in> ?DN" using 23 sorted_list_of_set by (metis "21" Diff_empty Suc_diff_le Suc_eq_plus1_left add_diff_cancel_right' card_Diff_subset diff_le_self empty_set hd_in_set le_bot not_less_bot not_less_eq order_refl)
hence "card ?Dn=card ?DN - 1" using 27 card_Diff_singleton 23 by metis
hence "card ?Dn = n & ?Rn \<subseteq> ?RN" using 21 22 by auto
hence "card ?Dn = n & ?Rn \<subseteq> Y" using 21 by fast
hence "?f \<in> G x Y n" using 24 25 26 21 G_def by blast
hence "?f \<in> F x Y n" using assms by fast
then obtain l::"'a list" where
1: "?f \<in> set (?B l Y) & (\<exists> A . (card A=n & A=set l))" using F_def by blast
obtain X where 
3: "card X=n & X=set l" using 1 by presburger
term "[ ?c R ?x Y . R <- ?B (?l A) Y ]"
have "?c ?f ?x Y \<in> set [ ?c R ?x Y . R <- ?B l Y ]" using 1 by simp
hence "g \<in> set (?B (?x # l) Y)" using 2 bijections_def by auto
let ?L="?x # l" have 
4: "set ?L={?x} \<union> set l" by simp
have "?x \<notin> set l" sorry hence "card (set ?L) = ?N" sorry
have "?c ?f ?x Y \<in> set [?c R ?x Y . R <- ?B (?l A) Y]" sorry
have "g \<in> set (concat [?c R ?x Y . R <- ?B (?l A) Y])" 
using 2 1 bijections_def sorry
have "?DN = insert ?x ?Dn & finite ?Dn & ?x \<notin> ?Dn" 
by (metis (hide_lams, no_types) "24" "27" Diff_iff `hd (sorted_list_of_set (Domain g)) \<in> Domain g` insertCI insert_Diff_single insert_subset set_diff_eq subset_antisym subset_refl)
hence "card ?Dn = n" using card_insert_disjoint 21 by (metis `card (Domain (g outside {hd (sorted_list_of_set (Domain g))})) = n \<and> Range (g outside {hd (sorted_list_of_set (Domain g))}) \<subseteq> Y`)
(* by (metis "0" `set (sorted_list_of_set XN) = XN` card_insert_if diff_Suc_1 insert_compr ll16 singleton_conv) *)
have "g \<in> F x Y (Suc n)" sorry
}
show "?GN \<subseteq> ?FN" sorry
qed

lemma fixes x Y n assumes "F x Y n \<subseteq> G x Y n" shows "F x Y (Suc n) \<subseteq>
 G x Y (Suc n)"
proof -
let ?F="% n::nat . (\<Union> 
{set (bijections (sorted_list_of_set X) Y) | X::('a::linorder set) . card X=n})"
let ?r="%x . runiq x"
let ?G="% n . {h . runiq h & runiq (inverse h) & card (Domain h)=n & 
Range h \<subseteq> Y}"
let ?Fn="?F n" let ?N="Suc n" let ?FN="?F ?N" let ?Gn="?G n" let ?GN="?G ?N"
(* hence 
3: "\<forall>z . (z \<in> ?F n \<longrightarrow> (z \<in> (?G n)))" using subsetD sorry *)
{ 
fix g
assume "g \<in> ?FN" then obtain XN::"'a::linorder set" where 
0: "card XN=?N & g \<in> set (bijections (sorted_list_of_set XN) Y)" by blast
have 
8: "finite XN" using 0 by (metis Zero_not_Suc card_infinite)
let ?lN="sorted_list_of_set XN" let ?x="hd ?lN" let ?ln="drop 1 ?lN"
let ?Xn="set ?ln"
have "size ?lN \<ge> 1" using 0 8 ll22
by (metis (full_types) One_nat_def le_SucI less_Suc0 not_le order_refl)
then have 
10: "?lN=?x # ?ln" 
by (metis drop_1_Cons hd.simps length_0_conv list.exhaust not_one_le_zero)
then have "remove1 ?x ?lN=?ln" using 8 by (metis remove1.simps(2))
also have "distinct ?lN" using 8 ll22 0 by auto
ultimately have "?Xn=set ?lN-{?x}" using set_remove1_eq by metis
also have "set ?lN=XN" using 8 0 by (metis sorted_list_of_set)
ultimately have 
14: "?Xn=XN-{?x}" by presburger
have "g \<in> set (bijections (?x # ?ln) Y)" using 0 10 by presburger
then have "g \<in> 
\<Union> {set a | a. a \<in> set ([ childrenof R ?x Y . R <- bijections ?ln Y ] )}" 
using 0 set_concat bijections_def 10 by auto
then obtain a where 
11: "g \<in> set a & a \<in> set [ childrenof R ?x Y . R <- bijections ?ln Y ]" by blast
obtain f where 
12: "a=childrenof f ?x Y & f \<in> set (bijections ?ln Y)" using 11 by auto
let ?ff="inverse f"
have "g \<in> set (childrenof f ?x Y)" using 11 12 by fast hence 
1: "f \<in> set (bijections ?ln Y) & g \<in> set (childrenof f ?x Y)" using 0 12 by fast
let ?e="% q . (f +* {(?x,q)})"
have "g \<in> set [ ?e y . y <- (sorted_list_of_set (Y - Range f))]" using 1 
childrenof_def by metis then
obtain y where 
15: "g = ?e y & y \<in> set (sorted_list_of_set (Y - Range f))" 
by auto 
assume "finite Y" then
have "finite (Y - Range f)" by (metis finite_Diff) hence
17: "g = f +* {(?x,y)} & y \<in> (Y -Range f)" using 15 sorted_list_of_set 8 by metis
have "?ln=sorted_list_of_set ?Xn" using 8 14 
by (metis `remove1 (hd (sorted_list_of_set XN)) (sorted_list_of_set XN) = drop 1 (sorted_list_of_set XN)` sorted_list_of_set_remove)
also have "card ?Xn=n" using 10 14 
by (metis "0" `distinct (sorted_list_of_set XN)` `set (sorted_list_of_set XN) = XN` diff_Suc_1 distinct_card distinct_drop length_drop)
ultimately have 
15: "f \<in> ?F n" using 1 by fastforce
assume "
\<Union> {set (bijections (sorted_list_of_set X) Y) | X::('a::linorder set) . card X=n}
\<subseteq>
{h . runiq h & runiq (inverse h) & card (Domain h)=n & Range h \<subseteq> Y}
" 
hence "f \<in> {h . runiq h & runiq (inverse h) & card (Domain h)=n & Range h \<subseteq> Y}" 
using 15 by blast 
hence "f \<in> ?G n" by fastforce
hence 5: "?r f & ?r ?ff & card (Domain f)=n & Range f \<subseteq> Y" by fast
have "set (sorted_list_of_set ?Xn)=?Xn" using 8 
by (metis `drop 1 (sorted_list_of_set XN) = sorted_list_of_set (set (drop 1 (sorted_list_of_set XN)))`) 
hence 
19: "Domain f=?Xn" using ll16 1 by metis
hence 7: "?x \<notin> (Domain f)" using 14 by blast
hence 8: "runiq g" using ll14 5 17 by metis have 
9: "runiq (inverse g)" using ll15 17 5 7 by metis
have 10: "Range g \<subseteq> Y" using 5 17 ll21 by fast
have "Domain g = Domain f \<union> Domain {(?x,y)}" using 17 ll20 by metis
also have "... = Domain f \<union> {?x}" by auto
ultimately have "Domain g=Domain f \<union> {?x}" by presburger
hence "card (Domain g)=?N" using 0 5 7 19 by force
hence "g \<in> ?G ?N" using 8 9 10 by fastforce
}
hence "?FN \<subseteq> ?GN" sorry
qed

(* value "childrenof {(0,0::nat),(1,1)} (2::nat) {0,1,2::nat,3}"
term "concat [ childrenof R x Y . R <- xs ]" term "childrenof" *)

end

