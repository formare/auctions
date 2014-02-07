theory g

imports f "../CombinatorialVickreyAuction"
"~~/src/HOL/Library/Code_Target_Nat"

begin

(* CL@MC: What's the rationale behind this?  Bringing allocation and bids into the 
   same structure, so that it is easier to compute a sum over them?  If so, this 
   will be worth mentioning in the paper, as it is an important design choice
   in formalisation. *)
type_synonym altbids = "(participant \<times> goods) \<Rightarrow> price"
type_synonym allocation_conv = "(participant \<times> goods) set"

abbreviation "altbids (b::bids) == split b"
term "altbids b"
term "(altbids (b::bids))=(x::altbids)"
(* CL: I don't understand the choice of the name "proceeds". *)
abbreviation "proceeds (b::altbids) (allo::allocation_conv) == setsum b allo"

lemma lll23: assumes "finite A" shows "setsum f A = setsum f (A \<inter> B) + setsum f (A - B)" using 
assms by (metis DiffD2 Int_iff Un_Diff_Int Un_commute finite_Un setsum.union_inter_neutral)

lemma shows "(P||(Domain Q)) +* Q = Q" by (metis Int_lower2 ll41 ll56)

lemma lll77: assumes "Range P \<inter> (Range Q)={}" "runiq (P\<inverse>)" "runiq (Q\<inverse>)" shows "runiq ((P \<union> Q)\<inverse>)"
using assms
by (metis Domain_converse converse_Un disj_Un_runiq)

lemma lll77b: assumes "Range P \<inter> (Range Q)={}" "runiq (P\<inverse>)" "runiq (Q\<inverse>)" shows "runiq ((P +* Q)\<inverse>)"
using lll77 assms subrel_runiq by (metis converse_converse converse_subset_swap paste_sub_Un)

lemma assumes "runiq P" shows "P\<inverse>``((Range P)-X) \<inter> ((P\<inverse>)``X) = {}"
using assms ll71 by blast

lemma lll78: assumes "runiq (P\<inverse>)" shows "P``(Domain P - X) \<inter> (P``X) = {}"
using assms ll71 by fast

lemma lll83: "P``X = P``(X \<inter> Domain P)" by blast

lemma lll84: "P``(X \<inter> Domain P)=P``X" by blast

lemma lll85: "Range (P||X) = P``X" 
proof -
  let ?p="P||X" let ?d=Domain let ?r=Range
  have "?r ?p=?p``(?d ?p)" by auto moreover have 
  "... = ?p``(X \<inter> ?d ?p)" using restrict_def by blast moreover have 
  "... \<subseteq> P``(X \<inter> ?d ?p)" using restrict_def by auto
  moreover have "... = P``X" by (metis Image_within_domain inf_commute inf_left_idem ll41)
  moreover have "P``X \<subseteq> ?r ?p" using restrict_def by fast
  ultimately show ?thesis by simp
qed

lemma lll82: assumes "(x::'a) \<in> Domain f" "runiq f" shows "f,,x = f,,,x"
(* CL: Interesting: metis says that eval_rel_def is unused in the proof, but when I use it,
   the proof takes much longer (too long for me to wait) *)
using assms by (metis Image_runiq_eq_eval cSup_singleton)

lemma lll79: assumes "\<Union> XX \<subseteq> X" "x \<in> XX" "x \<noteq> {}" shows "x \<inter> X \<noteq> {}" using assms by blast

lemma lll80: assumes "is_partition XX" "YY \<subseteq> XX" shows "(XX - YY) partitions (\<Union> XX - \<Union> YY)"
using is_partition_of_def is_partition_def assms
proof -
  let ?xx="XX - YY" let ?X="\<Union> XX" let ?Y="\<Union> YY"
  let ?x="?X - ?Y"
  have "\<forall> y \<in> YY. \<forall> x\<in>?xx. y \<inter> x={}" using assms is_partition_def by (metis Diff_iff set_rev_mp)
  then have "\<Union> ?xx \<subseteq> ?x" using assms by blast
  then have "\<Union> ?xx = ?x" by blast
  moreover have "is_partition ?xx" using subset_is_partition by (metis Diff_subset assms(1))
  ultimately
  show ?thesis using is_partition_of_def by blast
qed

lemma lll81a: assumes "a \<in> possible_allocations_rel G N" shows
"runiq a & runiq (a\<inverse>) & (Domain a) partitions G & Range a \<subseteq> N" 
proof -
  obtain Y where
  0: "a \<in> injections Y N & Y \<in> all_partitions G" using assms possible_allocations_rel_def by auto
  show ?thesis using 0 injections_def by (smt all_partitions_def mem_Collect_eq)
qed

lemma lll81b: assumes "runiq a" "runiq (a\<inverse>)" "(Domain a) partitions G" "Range a \<subseteq> N"
shows "a \<in> possible_allocations_rel G N"
proof -
  have "a \<in> injections (Domain a) N" unfolding injections_def using assms(1) assms(2)  assms(4) by blast
  moreover have "Domain a \<in> all_partitions G" using assms(3) all_partitions_def by fast
  ultimately show ?thesis using assms(1) possible_allocations_rel_def by auto
qed

lemma lll81: "a \<in> possible_allocations_rel G N \<longleftrightarrow>
runiq a & runiq (a\<inverse>) & (Domain a) partitions G & Range a \<subseteq> N"
using lll81a lll81b by blast

lemma lll74: assumes "a\<inverse> \<in> possible_allocations_rel G N" 
"Y2 \<inter> (G - a,,,x)={}"
"Y2 \<noteq> {}"
shows "(a +< (x,Y2))\<inverse> \<in> possible_allocations_rel (G-(a,,,x)\<union>Y2) (N \<union> {x})"
proof -
let ?Y1="a,,,x" let ?u=runiq let ?A=possible_allocations_rel let ?aa="a\<inverse>" let ?I=injections
let ?P=all_partitions let ?r=Range let ?a2="a +< (x, Y2)" let ?d=Domain
obtain pG where 
1: "?aa \<in> ?I pG N & pG \<in> ?P G" using assms(1) possible_allocations_rel_def by fastforce
have "?u a" using 1 injections_def
by (smt converse_converse mem_Collect_eq)
then have 
12: "?u (a +< (x,Y2))" using lll73 by metis
have "?r (a -- x)=a``(?d a - {x})" using Outside_def by blast
moreover have 
0: "?u ?aa & ?u a" using assms by (metis `runiq a` lll81) ultimately
have "?r (a -- x) \<inter> (a``{x}) = {}" using lll78 
by metis 
moreover have 
3: "(a -- x) \<union> {(x, Y2)} = ?a2" using paste_def 
by (metis Domain_empty Domain_insert fst_conv snd_conv)
have 
6: "?r ?a2 = ?r (a -- x) \<union> {Y2}" using 3 by auto
moreover have "?r a = ?r (a -- x) \<union> (a``{x})" using Outside_def
by blast
ultimately moreover have "?r (a -- x) = ?r a - a``{x}" by auto
moreover have "is_partition (?r a) & (\<Union> (?r a))=G" using 1 by (metis Domain_converse assms(1) is_partition_of_def lll81)
ultimately moreover have "a``{x} \<subseteq> ?r a" by (metis Un_upper2)
ultimately have 
5: "(?r (a -- x)) partitions (G - \<Union>(a``{x}))" using lll80 by metis
then have 
4: "\<Union> (?r (a -- x)) = (G - a,,,x)" unfolding is_partition_of_def by fast
then have "Y2 \<notin> (?r (a -- x))" using lll79 assms subsetI by metis
then have "?r {(x, Y2)} \<inter> ?r (a -- x) = {}" using assms by blast
moreover have "?u {(x, Y2)}" by (metis runiq_singleton_rel)
moreover have "(a--x)\<inverse> \<subseteq> ?aa" using Outside_def
by blast
moreover then  have "?u ((a -- x)\<inverse>)" using 0 subrel_runiq by metis
ultimately moreover have "?u (((a -- x) \<union> {(x, Y2)})\<inverse>)" using 0 by (metis 
IntI Range_insert empty_iff insert_iff runiq_conv_extend_singleton)
ultimately have 
11: "?u (?a2\<inverse>)" using 3 by metis
moreover have "?d a \<subseteq> N" using assms lll81 by simp
moreover have "?d {(x, Y2)}={x}" by simp
ultimately moreover have "?r (?a2\<inverse>) \<subseteq> N \<union> {x}" using paste_Domain
by (smt Domain_insert Range_converse Un_iff fst_conv set_rev_mp subsetI)
ultimately have 
13: "?a2\<inverse> \<in> injections (?r ?a2) (N \<union> {x})" using 12
 Domain_converse converse_converse injectionsI by (metis (hide_lams, no_types))
have "Y2 \<inter> \<Union> (?r (a -- x)) = {}" using 4 assms by presburger
moreover have "is_partition (?r (a --x ))" using 5 by (metis is_partition_of_def)
ultimately have "is_partition (insert Y2 (?r (a -- x)))" using partition_extension1 assms
by blast
then have "is_partition (?r (a -- x) \<union> {Y2})" by auto
then have "is_partition (?r ?a2)" by (metis "6")
moreover have "\<Union> (?r ?a2) = \<Union> (?r (a -- x)) \<union> Y2"
by (metis "6" Union_Un_distrib cSup_singleton)
moreover have "... = (G - (a,,,x)) \<union> Y2" by (metis "4")
ultimately have "(?r ?a2) partitions ((G - (a,,,x)) \<union> Y2)"
by (metis "6" Un_commute insert_def is_partition_of_def singleton_conv)
then have "?r ?a2 \<in> ?P (G - (a,,,x) \<union> Y2)" using all_partitions_def by (metis mem_Collect_eq)
then have "(?a2\<inverse>) \<in> injections (?r ?a2) (N \<union> {x}) & ?r ?a2 \<in> ?P (G - (a,,,x) \<union> Y2)"
using 13 by fast
then show ?thesis using possible_allocations_rel_def by auto
qed

lemma lll75: assumes "finite a" "(b::altbids) (xx, yy1) \<le> b (xx, yy2)" shows 
"setsum b ((a::allocation_conv) +< (xx,yy1)) \<le> setsum b (a +< (xx,yy2))"
proof -
  let ?z1="(xx, yy1)" let ?z2="(xx, yy2)" let ?a0="a -- xx" let ?a1="a +< ?z1" let ?a2="a +< ?z2"
  have 
  0: "{?z1} || {xx}={?z1} & {?z2}||{xx}={?z2}" using restrict_def by auto

  have "finite {?z1} & finite {?z2}" by simp then have 
  2: "finite ?a1 & finite ?a2" using paste_def assms 
  by (metis finite_Un finite_insert outside_union_restrict)

  have "?a1 = (?a1 -- xx) \<union> (?a1 || {xx}) " 
  using paste_def Outside_def outside_union_restrict by metis
  have "setsum b ?a1 = setsum b (?a1||{xx}) + setsum b (?a1 outside {xx})" using 2
  by (metis finite_Un lll00 lll01 lll06b outside_union_restrict setsum.union_disjoint)
  moreover have 
  1: "?a1 = a +* {?z1} & ?a2 = a +* {?z2}" by (metis fst_conv snd_conv)
  then have "?a1||{xx} = (a || {xx}) +* ({?z1} || {xx})" using lll71 by fastforce

  moreover have "... = {?z1}||{xx}" using ll41 ll56 by (metis "0" Domain_empty Domain_insert Int_lower2)
  ultimately have 
  "setsum b ?a1 = setsum b ({?z1}) + setsum b (?a1 outside {xx})" 
  by (metis "0") then have
  11: "setsum b ?a1 = b ?z1 + setsum b (?a1 outside {xx})"
  by simp

  have "setsum b ?a2 = setsum b (?a2||{xx}) + setsum b (?a2 outside {xx})" using 2
  by (metis finite_Un lll00 lll01 lll06b outside_union_restrict setsum.union_disjoint)
  have "?a2||{xx} = (a || {xx}) +* ({?z2} || {xx})" using lll71 by fastforce
  moreover have "... = {?z2}||{xx}" using ll41 ll56 by (metis "0" Domain_empty Domain_insert Int_lower2)
  ultimately have "setsum b ?a2 = setsum b ({?z2}) + setsum b (?a2 outside {xx})" using 1 0  by (metis 
  `proceeds b (a +< (xx, yy2)) = proceeds b ((a +< (xx, yy2)) || {xx}) + proceeds b ((a +< (xx, yy2)) -- xx)`) 
  then have
  12: "setsum b ?a2 = b ?z2 + setsum b (?a2 outside {xx})" by simp

(*
  have "?a2 = (?a2 -- xx) \<union> (?a2 || {xx})" 
  using paste_def Outside_def outside_union_restrict by metis
  moreover
  have "finite ?a2" sorry
  moreover have "?a2||{xx} = (a || {xx}) +* ({?z2} || {xx})" using lll71
  1 by fastforce
  moreover have "... = {?z2}||{xx}" using ll41 ll56 
  by (metis (hide_lams, no_types) "0" Domain_empty Domain_insert Int_lower2)
  ultimately have "setsum b ?a2 = setsum b ({?z2}) + setsum b (?a2 outside {xx})" 
  using 0 2 sledgehammer
  then have
  12: "setsum b ?a2 = b ?z2 + setsum b (?a2 outside {xx})"
  by simp
*)

  have "?a1 outside {xx} = (a outside {xx}) +* ({?z1} outside {xx})" 
  using lll72 by (metis "1")
  moreover have "... = (a outside {xx}) +* {}" using 1
  by (metis "0" Diff_insert_absorb empty_iff lll04 restrict_empty)
  ultimately have "?a1 outside {xx} = a outside {xx}"
  by (metis Un_empty_right outside_union_restrict paste_outside_restrict restrict_empty)
  moreover have "... = ?a2 outside {xx}" using lll72 0 1 lll04 
  Un_empty_right outside_union_restrict paste_outside_restrict restrict_empty 
  by (metis Diff_cancel) (*MC: Diff_insert_absorb AND empty_iff not needed now??! *)
  ultimately show ?thesis using 11 12 assms by smt
qed

lemma lll86: assumes "X \<inter> Y={}" shows "R``X = (R outside Y)``X"
using assms Outside_def Image_def by blast

lemma lll76: assumes "a \<in> possible_allocations_rel G N"
"n \<in> Range a"
"finite (possible_allocations_rel G (N-{n}))" (*MC: qv allocs_finite *)
"finite a" (*MC: the two finiteness requirements can be replaced by finiteness of N, G*)
"EX i. i\<in>Domain (a^-1 -- n) & b (i, (a^-1),,,i) \<le> b (i, (a^-1),,,i \<union> (a^-1),,,n)"
(* MC: this is monotonicity assumption *)
shows "Max (proceeds b ` (converse ` (possible_allocations_rel G (N - {n})))) \<ge> 
proceeds b ((a\<inverse>) -- n)"
proof -
  let ?P=possible_allocations_rel let ?aa="a^-1 -- n" let ?d=Domain let ?Yn="a^-1,,,n"
  let ?p=proceeds let ?X="converse ` (?P G (N-{n}))" let ?u=runiq let ?r=Range 

  have "?u a & ?u (a^-1)" using assms(1) lll81 by blast
  then moreover have "?u ?aa" using subrel_runiq Outside_def by blast
  moreover have "?aa \<subseteq> a^-1" using Outside_def by blast
  then moreover have "?aa^-1 \<subseteq> a" using Outside_def converse_def by (metis converse_subset_swap)
  ultimately have 
  2: "?u ?aa & ?u a & ?u (a^-1) & ?u (?aa^-1)" using subrel_runiq by auto obtain i where 
  0: "i \<in> ?d ?aa & b (i, (a^-1),,,i) \<le> b (i, (a^-1),,,i \<union> ?Yn)" using assms(5) by blast
  let ?Y1="?aa,,,i" let ?Y2="?Y1 \<union> ?Yn"
  
  have "{i} \<inter> {n}={}" using 0 by (metis Diff_iff Int_commute Int_empty_right Int_insert_right_if0 outside_reduces_domain)
  then have "?aa``{i} = (a^-1)``{i}" using 0 Outside_def Image_def lll86 by metis then
  have 
  7: "?Y1=(a^-1),,,i" by simp

  have 
  5: "?d ?aa \<subseteq> N - {n}" using assms lll81 by (metis Diff_mono Range_converse converse_converse outside_reduces_domain subset_refl)
  then have 
  6: "N - {n} \<union> {i} = N -{n}" using 0 by blast
  have
  3: "is_partition_of (?d a) G" using assms lll81 by blast then
  have "is_partition (?r (a^-1))" using  is_partition_of_def by (metis Range_converse)
  then have 
  4: "is_partition (?r ?aa)" using all_partitions_def is_partition_of_def 
  Outside_def subset_is_partition lll81 assms by (metis Range_outside_sub equalityE)
  moreover have "?Y1 \<in> (?r ?aa)" using 0 lll82 by (metis "2" eval_runiq_in_Range)
  ultimately have "?Y2 \<noteq> {}" using is_partition_def 0 by (metis Un_empty  inf_bot_right)

  have "{i} \<times> ?aa``{i} = {i} \<times> {?Y1}" using 0 Image_runiq_eq_eval 2 by (metis cSup_singleton)
  moreover have "... = {(i, ?Y1)}" by simp
  ultimately have 
  1: "?aa +< (i, ?Y1) = ?aa" using 0 paste_def eval_rel_def ll84 by (metis fst_conv snd_conv)
  
  have "?r (a^-1) = ?r ?aa \<union> ?r ((a^-1)||{n})" by (metis Range_Un_eq outside_union_restrict)
  moreover have "... = ?r ?aa \<union> (a^-1) `` {n}" by (metis lll85)
  ultimately moreover have "?r ?aa = (a^-1)``(?d (a^-1)-{n})" by (metis lll01 lll85)
  ultimately moreover have "?r (a^-1) = ?r ?aa \<union> (a^-1)``{n}" by simp
  ultimately moreover have "?r ?aa \<inter> (a^-1)``{n} = {}" using lll78
  by (metis "2" converse_converse)
  ultimately have "?r ?aa=?r (a^-1) - (a^-1)``{n}" by blast
  moreover have "a^-1``{n} = {?Yn}"
  by (metis "2" Domain_converse Image_runiq_eq_eval assms(2) lll82)
  ultimately have "?r ?aa = ?r (a^-1) - {?Yn}" by force
  moreover have "{?Yn} \<subseteq> ?r (a^-1)" using assms eval_runiq_in_Range by (metis "2" Domain_converse cSup_singleton empty_subsetI insert_subset runiq_wrt_eval_rel')
  moreover have "\<Union> (?r (a^-1))=G" using assms lll81 is_partition_of_def by (metis Range_converse)
  ultimately
  have "is_partition_of (?r ?aa) (G - ?Yn)" using lll80 3 2 4 
  by (metis `is_partition (Range (a\<inverse>))` cSup_singleton)
  moreover have "?u ?aa" by (metis "2")
  moreover have "?u (?aa^-1)" using 2 by fast
  moreover have "?d ?aa \<subseteq> (N -{n})" by (metis Diff_mono Domain_converse assms lll81 outside_reduces_domain subset_refl)

  ultimately have "?aa^-1 \<in> ?P (G-?Yn) (N-{n})" using assms lll81 by (metis Domain_converse converse_converse)

  moreover have "?Y2 \<inter> (G -?Yn - ?Y1)={}" by fast
  ultimately have "(?aa +< (i, ?Y2))\<inverse> \<in> ?P (G - ?Yn - ?Y1 \<union> ?Y2) (N-{n} \<union> {i})" 
  using lll74 by (metis `(a\<inverse> -- n) ,,, i \<union> a\<inverse> ,,, n \<noteq> {}`)
  then have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P (G \<union> ?Y2) (N-{n} \<union> {i})" by (smt Un_Diff_cancel Un_commute Un_left_commute)

  moreover have "?Yn \<subseteq> G"
  by (metis Union_upper `\<Union>Range (a\<inverse>) = G` `{a\<inverse> ,,, n} \<subseteq> Range (a\<inverse>)` insert_subset)
  moreover have "\<Union> (?r ?aa) \<subseteq> G"
  by (metis Diff_subset Sup_subset_mono `Range (a\<inverse> -- n) = Range (a\<inverse>) - {a\<inverse> ,,, n}` `\<Union>Range (a\<inverse>) = G`)
  then moreover have "?Y1 \<subseteq> G" 
  by (metis Sup_le_iff `(a\<inverse> -- n) ,,, i \<in> Range (a\<inverse> -- n)`)
  ultimately moreover have "?Y2 \<subseteq> G" by simp
  ultimately have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P G ((N-{n}) \<union> {i})" by (metis Un_absorb2)
  then have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P G (N-{n})" using 6 by force
  then have "?aa +< (i, ?Y2) \<in> ?X" by (metis converse_converse image_eqI)
  then have "?p b (?aa +< (i, ?Y2)) \<in> (?p b)`?X" by blast
  moreover have "finite (?p b ` ?X)" using assms(3) by (metis finite_imageI)
  ultimately have "?p b (?aa +< (i, ?Y2)) \<le> Max ((?p b) ` ?X)" using Max_ge by blast
  moreover have "b (i, ?Y1) \<le> b (i, ?Y2)" using 7 0 by presburger
  moreover have "finite ?aa" using assms(4) by (metis `a\<inverse> -- n \<subseteq> a\<inverse>` finite_converse finite_subset)
  ultimately moreover have " ?p b (?aa +< (i, ?Y2)) \<ge> ?p b (?aa +< (i, ?Y1))" using lll75
  by blast
  ultimately show ?thesis  using 1 by force
qed

lemma "value_rel (b::bids) a = proceeds (altbids b) (a^-1)" using value_rel_def split_def 
sorry

corollary assumes "runiq (P^-1)" shows "Range (P outside X) \<inter> Range (P || X)={}"
using assms lll78 Outside_def Range_def by (metis lll01 lll85)

end

