theory g

imports f "../CombinatorialVickreyAuction"
"~~/src/HOL/Library/Code_Target_Nat"

begin

type_synonym altbids = "(participant \<times> goods) \<Rightarrow> price"
type_synonym altallo = "(participant \<times> goods) set"

abbreviation "altbids (b::bids) == split b"
term "altbids b"
term "(altbids (b::bids))=(x::altbids)"
abbreviation "proceeds (b::altbids) (allo::altallo) == setsum b allo"

lemma lll23: assumes "finite A" shows "setsum f A = setsum f (A \<inter> B) + setsum f (A - B)" using 
assms by (metis DiffD2 Int_iff Un_Diff_Int Un_commute finite_Un setsum.union_inter_neutral)

lemma shows "(P||(Domain Q)) +* Q = Q"  using restrict_def paste_def
by (metis Int_lower2 ll41 ll56)

lemma lll74: assumes "a^-1 \<in> possible_allocations_rel G N" "Y2 \<inter> (G - a,,x)={}"
shows "(a +< (x,Y2))^-1 \<in> possible_allocations_rel (G-(a,,x)\<union>Y2) (N \<union> {x})"
proof -
let ?Y1="a,,x" let ?u=runiq let ?A=possible_allocations_rel let ?aa="a^-1" let ?I=injections
let ?P=all_partitions let ?r=Range let ?a2="a +< (x, Y2)"
obtain pG where 
1: "?aa \<in> ?I pG N & pG \<in> ?P G" using assms(1) possible_allocations_rel_def by fastforce
have "?u a" using 1 injections_def
by (smt converse_converse mem_Collect_eq)
then have "?u (a +< (x,Y2))" using lll73 by metis
have "is_partition (?r a)" using assms 1 sorry
then have "is_partition (?r a \<union> {Y2})" using assms is_partition_def sorry
have "?r ?a2 \<subseteq> ?r a \<union> {Y2}" by (metis Range_empty Range_insert paste_Range snd_conv)
show ?thesis sorry
qed

lemma lll75: assumes "finite a" "(b::altbids) (xx, yy1) \<le> b (xx, yy2)" shows 
"setsum b ((a::altallo) +< (xx,yy1)) \<le> setsum b (a +< (xx,yy2))"
proof -
let ?z1="(xx, yy1)" let ?z2="(xx, yy2)" let ?a0="a -- xx" let ?a1="a +< ?z1" let ?a2="a +< ?z2"
have 
0: "{?z1} || {xx}={?z1} & {?z2}||{xx}={?z2}" using restrict_def by auto
have "?a1 = (?a1 -- xx) \<union> (?a1 || {xx}) " 
using paste_def Outside_def outside_union_restrict by metis
moreover have "finite ?a1" sorry
ultimately have "setsum b ?a1 = setsum b (?a1||{xx}) + setsum b (?a1 outside {xx})" 
by (metis finite_Un lll00 lll01 lll06b outside_union_restrict setsum.union_disjoint)
moreover have 
1: "?a1 = a +* {?z1} & ?a2 = a +* {?z2}"
by (metis fst_conv snd_conv)
then have "?a1||{xx} = (a || {xx}) +* ({?z1} || {xx})" using lll71
by fastforce
moreover have "... = {?z1}||{xx}" using ll41 ll56 by (metis "0" Domain_empty Domain_insert Int_lower2)
ultimately have 
"setsum b ?a1 = setsum b ({?z1}) + setsum b (?a1 outside {xx})" 
by (metis "0") then have
11: "setsum b ?a1 = b ?z1 + setsum b (?a1 outside {xx})"
by simp
have "?a1 = (?a1 -- xx) \<union> (?a1 || {xx}) " 
using paste_def Outside_def outside_union_restrict by metis
moreover
have "finite ?a2" sorry
moreover have "?a2||{xx} = (a || {xx}) +* ({?z2} || {xx})" using lll71
1 by fastforce
moreover have "... = {?z2}||{xx}" using ll41 ll56 
by (metis (hide_lams, no_types) "0" Domain_empty Domain_insert Int_lower2)
ultimately have "setsum b ?a2 = setsum b ({?z2}) + setsum b (?a2 outside {xx})" 
using 0 sorry
then have
12: "setsum b ?a2 = b ?z2 + setsum b (?a2 outside {xx})"
by simp
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

lemma lll76: shows "Max (proceeds b ` (converse ` (possible_allocations_rel G (N - {n})))) \<ge> 
proceeds b ((a^-1) -- n)"
proof -
  let ?P=possible_allocations_rel let ?aa="a^-1 -- n" let ?d=Domain let ?Yn="a^-1,,n"
  let ?p=proceeds let ?X="converse ` (?P G (N-{n}))" let ?u=runiq
  have "?aa \<noteq> {}" sorry then
  obtain i where 
  0: "i \<in> ?d ?aa" by auto
  let ?Y1="?aa,,i" let ?Y2="?Y1 \<union> ?Yn"
  have "?u ?aa" sorry then have 
  "{i} \<times> ?aa``{i} = {i} \<times> {?Y1}" using 0 by (metis Image_runiq_eq_eval)
  moreover have "... = {(i, ?Y1)}" by simp
  ultimately have 
  1: "?aa +< (i, ?Y1) = ?aa" using 0 paste_def eval_rel_def ll84 by (metis fst_conv snd_conv)
  have "?aa^-1 \<in> ?P (G-?Yn) (N-{n})" sorry
  moreover have "?Y2 \<inter> (G -?Yn - ?aa,,i)={}" sorry
  ultimately have "(?aa +< (i, ?Y2))^-1 \<in> ?P (G - ?Yn - ?Y1 \<union> ?Y2) (N-{n} \<union> {i})" 
  using lll74 by metis
  then have 
  "(?aa +< (i, ?Y2))^-1 \<in> ?P (G \<union> ?Y2) (N-{n} \<union> {i})" by (smt Un_Diff_cancel Un_commute Un_left_commute)
  then have 
  "(?aa +< (i, ?Y2))^-1 \<in> ?P G (N-{n})" sorry
  then have "?aa +< (i, ?Y2) \<in> ?X" by (metis converse_converse image_eqI)
  then have "?p b (?aa +< (i, ?Y2)) \<in> (?p b)`?X" by blast
  moreover have "finite (?p b ` ?X)" sorry
  ultimately have "?p b (?aa +< (i, ?Y2)) \<le> Max ((?p b) ` ?X)" using Max_ge by blast
  moreover have "b (i, ?Y1) \<le> b (i, ?Y2)" sorry
  moreover have "finite ?aa" sorry
  ultimately moreover have " ?p b (?aa +< (i, ?Y2)) \<ge> ?p b (?aa +< (i, ?Y1))" using lll75
  by blast
  ultimately show ?thesis  using 1 by force
qed


notepad
begin
let ?d=Domain let ?r=Range let ?u=runiq
fix G::goods fix N::"participant set" fix b::"altbids" fix a::"altallo" fix n::"participant" fix z let ?Gn="a,,n" 
have 
2: "a^-1 \<in> possible_allocations_rel G N" sorry 
then obtain Y where 
3: "a^-1 \<in> injections Y N \<and> Y \<in> all_partitions G" using possible_allocations_rel_def
by force
have "?u ((a^-1)^-1) & ?u (a^-1)" using 3 by (smt injections_def mem_Collect_eq)
then have "?u a & ?u (a^-1)" by simp
then have "?u a" by auto then have
0: "?u (a -- n)" using runiq_def by (metis l39 lll12 trivial_subset)
have "{z} \<subseteq> a -- n" sorry let ?m="fst z" let ?Gm="snd z" have "{z} \<subseteq> a -- n" sorry 
moreover have 
1: "finite (a -- n)" sorry ultimately have 
"(setsum b (a -- n)) = b z + setsum b ((a -- n) - {z})" 
by (smt insert_subset setsum_diff1_ring)
moreover have "... \<le> b (?m, ?Gm \<union> ?Gn) + setsum b ((a -- n) - {z})" sorry (*monotonicity of b assumption needed *)
(* moreover have "Domain {z} \<inter> Domain ((a -- n) - {z})= {}" using 0 lll33 runiq_def sorry *)
then moreover have "(?m, ?Gm \<union> ?Gn) \<notin> (a -- n) - {z}" using 0 runiq_def sorry
ultimately have "setsum b (a -- n) \<le> setsum b ((a -- n) - {z} \<union> {(?m, ?Gm \<union> ?Gn)})" 
using 1 by force
let ?aa="(a -- n) - {z} \<union> {(?m, ?Gm \<union> ?Gn)}"
have "runiq ?aa" using fst_conv
by (metis (hide_lams, no_types) "0" `{z} \<subseteq> a -- n`  insert_subset runiq_replace_snd' surj_pair)
have "?r ?aa = (?r (a -- n)) - {?Gm} \<union> {?Gm \<union> ?Gn}" sorry
end

lemma "value_rel (b::bids) a = proceeds (altbids b) (a^-1)" using value_rel_def sorry

definition goo where 
"goo (b::bids) (xx:: (participant \<times> goods) set) = setsum (%n. (b n) (xx,,n)) (Domain xx)"
lemma shows "goo b (x^-1) = value_rel b x" sorry
lemma shows "remaining_value_rel G N t b n = goo b ((winning_allocation_rel G N t b)^-1 -- n)" sorry

lemma assumes 
"(xx^-1) \<in> possible_allocations_rel G N"
shows "((xx -- n) +< {(i, xx,,i \<union> xx,,n)})^-1 \<in> possible_allocations_rel G (N-{n})" sorry

lemma shows "goo b ((xx::allo) -- (n::participant)) \<le> goo b ((xx -- n) +< {(i, xx,,i \<union> xx,,n)})"
proof -
let ?Gn="xx,,n" let ?Gi="xx,,i" let ?GI="?Gi \<union> ?Gn" 
let ?d="Domain" let ?yy="xx -- n" let ?zz="?yy +< {(i, ?GI)}" let ?f="%j. (b j) (?yy,,j)"
let ?g="%j. (b j) (?zz,,j)"
have 
"?GI = ?zz,,i" using paste_def sorry
moreover have 
"b i (?yy,,i) \<le> b i (?GI)" sorry
ultimately 
have 
"?f i \<le> ?g i" by metis
moreover have 
"\<forall> j. j \<noteq> i \<longrightarrow> ?yy,,j = ?zz,,j" using paste_def eval_rel_def sorry
ultimately moreover have "\<forall>j. ?f j \<le> ?g j" by (metis (full_types) dual_order.refl)
moreover have "?d ?yy = ?d ?zz" sorry
ultimately
show ?thesis using goo_def by (metis (mono_tags) setsum_mono)
qed

notepad
begin
fix G N n P

end
end

