theory g

imports "../CombinatorialVickreyAuction"
"~~/src/HOL/Library/Code_Target_Nat"
(* "../CombinatorialVickreyAuctionSoundness" *)
"../CombinatorialAuctionProperties"
Relation

begin

abbreviation "allInjections == {R. (runiq R) & (runiq (R^-1))}"

lemma "injections' X Y \<subseteq> allInjections" by fast
lemma "injections' X Y = {R. Domain R = X & Range R \<subseteq> Y} \<inter> allInjections" by fastforce

lemma fixes N::"participant set" fixes G::goods fixes a::"allocation" assumes 
"a \<in> possibleAllocationsRel N G" shows 
"a^-1 \<in> injections (Range a) N & Range a partitions G & Domain a \<subseteq> N"
using assms all_partitions_def Domain_converse allocation_injective converse_converse 
image_iff injections_def mem_Collect_eq by smt

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

lemma lll82: assumes "(x::'a) \<in> Domain (f::(('a \<times> ('b set)) set))" "runiq f" shows "f,,x = f,,,x"
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
"setsum b ((a::allocation) +< (xx,yy1)) \<le> setsum b (a +< (xx,yy2))"
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

(*
lemma shows 
(*remaining_value_rel G N t b n*)
"setsum 
(%m. (b m (eval_rel_or ((winning_allocation_rel G N t b)\<inverse>) m {})) )
(N-{n})
= setsum (altbids b) ((winning_allocation_rel G N t b)^-1 -- n)"
using remaining_value_rel_def winning_allocation_rel_def Outside_def 
proof -
let ?w="winning_allocation_rel" let ?W="?w G N t b"
term "altbids b"
term "(?W^-1)"
  {
    fix m let ?M="(m, (?W^-1),,m)"
    assume "m \<in> (N-{n})" then
    have "card (?W^-1 `` {m}) \<noteq> 0" sledgehammer
    have "b m (eval_rel_or (?W^-1) m {}) = (altbids b) ?M" 
    using eval_rel_or_def winning_allocation_rel_def sorry
    have "True" sorry
  }
  show ?thesis sorry
qed
*)

lemma lll76: assumes "a \<in> possible_allocations_rel G N"
"n \<in> Range a"
"finite (possibleAllocationsRel (N-{n}) G)"
(* "finite (possible_allocations_rel G (N-{n}))" (*MC: qv allocs_finite *) *)
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
  3: "(?d a) partitions G" using assms lll81 by blast then
  have "is_partition (?r (a^-1))" using is_partition_of_def by (metis Range_converse)
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

corollary lm01:
assumes "a \<in> possibleAllocationsRel N G"
"n \<in> Domain a"
"finite (possibleAllocationsRel (N-{n}) G)" (*MC: qv allocs_finite *)
"finite a" (*MC: the two finiteness requirements can be replaced by finiteness of N, G*)
"EX i. i\<in>Domain (a -- n) & b (i, a,,,i) \<le> b (i, a,,,i \<union> a,,,n)"
(* MC: this is monotonicity assumption *)
shows "alpha N G b n \<ge> 
proceeds b (a -- n)" using lll76 assms converse_def 
proof -
  let ?p="possible_allocations_rel" let ?a="a^-1" let ?f=finite
  have "?a \<in> ?p G N" using assms by fastforce
  moreover have "n \<in> Range ?a" using assms
by fast
  moreover have "?f ?a" using assms by fast
  moreover have 
"EX i. i\<in>Domain (?a^-1 -- n) & b (i, (?a^-1),,,i) \<le> b (i, (?a^-1),,,i \<union> (?a^-1),,,n)"
using assms 
by simp
ultimately have 
"Max (proceeds b ` (converse ` (?p G (N - {n})))) \<ge> 
proceeds b ((?a\<inverse>) -- n)" using lll76 assms by blast
thus ?thesis by simp
qed

lemma lm02: "arg_max' f A = { x \<in> A . f x = Max (f ` A) }" using assms
by simp

abbreviation "isChoice R == \<forall>x. R``{x} \<subseteq> x"

lemma lm04: "graph (X \<inter> Y) f \<subseteq> graph X f || Y" using graph_def assms restrict_def
by (smt Int_iff mem_Collect_eq restrict_ext subrelI)

lemma lm06: "graph X f = Graph f || X" using graph_def Graph_def restrict_def
by (smt inf_top.left_neutral  lm04 mem_Collect_eq prod.inject restrict_ext subsetI subset_antisym)

lemma lm05: "graph (X \<inter> Y) f = graph X f || Y" using lll02 lm06 by metis

lemma lm07: assumes "isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))" shows 
"t (winningAllocationsRel N G b) \<in> winningAllocationsRel N G b" 
using assms
proof - (* MC: to be cleaned *)
let ?W="winningAllocationsRel N G b" let ?T="graph {?W} t" let ?TT="graph UNIV t" let ?TTT="Graph t"
have "?T``{?W} \<subseteq> ?W" using assms by fast
moreover have "?TTT``{?W} = (?TTT || {?W})``{?W}" using restrict_def Image_def by fast
moreover have "?TTT || {?W} = ?TT || {?W}" using ll36 by metis
moreover have "... = ?T" using graph_def restrict_def Graph_def lm05 by (metis Int_UNIV_left)
moreover have "?T``{?W} = ?TTT``{?W}" using graph_def Graph_def by (metis calculation(2) lm06)
moreover have "?T``{?W} \<subseteq> t`{?W}" using l4 l5 ll36 by (metis calculation(5) subsetI)
ultimately show ?thesis using assms by (metis (hide_lams, no_types) image_eqI insertI1 l4 set_rev_mp)
qed

corollary lm03: "winningAllocationsRel N G (b::altbids) \<subseteq> possibleAllocationsRel N G" 
using assms lm02 by (smt mem_Collect_eq subsetI)

corollary lm08: assumes 
"a \<in> winningAllocationsRel N G b"
"n \<in> Domain a"
"finite (possibleAllocationsRel (N-{n}) G)"
"finite a"
"EX i. i\<in>Domain (a -- n) & b (i, a,,,i) \<le> b (i, a,,,i \<union> a,,,n)"
(* MC: this is monotonicity assumption *)
shows "alpha N G b n \<ge> 
proceeds b (a -- n)" using assms lm01 lm03 by simp

corollary assumes 
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))"
"n \<in> Domain (winningAllocationRel N G t b)" 
"finite (possibleAllocationsRel (N-{n}) G)"
"finite (winningAllocationRel N G t b)"
"EX i. i\<in>Domain ((winningAllocationRel N G t b) -- n) & 
b (i, (winningAllocationRel N G t b),,,i) \<le> 
b (i, (winningAllocationRel N G t b),,,i \<union> (winningAllocationRel N G t b),,,n)"
shows "alpha N G b n \<ge> remainingValueRel N G t b n"
using lm08 assms lm07 by blast

lemma assumes "n \<notin> N" shows "Max ((proceeds b)`(possibleAllocationsRel (N-{n}) G)) = 
proceeds b (winningAllocationRel N G t b -- n)" using assms sorry

corollary assumes "runiq (P^-1)" shows "Range (P outside X) \<inter> Range (P || X)={}"
using assms lll78 by (metis lll01 lll85)

value "{(0::nat,10),(1,11),(1,12::nat)} ,, 0"
value "({(0::nat,10),(1,11),(1,12)} +< (1,13::nat)) ,, 1"
term "%x. (R,,x)"

end

