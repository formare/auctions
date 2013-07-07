theory a
imports Main 
begin

definition is_partition where 
"is_partition X = (\<forall> x1 \<in> X . x1 \<noteq> {} & (\<forall> x2 \<in> X - {x1}. x1 \<inter> x2 = {}))"

definition is_partition_of where "is_partition_of X XX = ((\<Union> X = XX) & is_partition X)"

lemma a1: fixes XX X assumes "is_partition_of X XX" shows " X \<subseteq> Pow XX"
proof -
(* fix XX X *)
(* assume 1: "is_partition_of X XX"*)
have "X \<subseteq> Pow (\<Union> X)" using subset_Pow_Union by blast
thus "X \<subseteq> Pow XX" using is_partition_of_def assms by (metis Pow_def)
qed

lemma a2: fixes x shows "Pow {x} = {{},{x}}" using Pow_insert by (metis Pow_empty Un_empty_left Un_insert_left image_empty image_insert)

lemma a3: fixes x X assumes "is_partition_of X {x}" shows "X={{x}}"
proof -
have 1: "X \<subseteq> {{},{x}}" using a1 a2 assms by blast
have 2: "\<not> {} \<in> X" using is_partition_def assms is_partition_of_def by metis
have 3: "X \<noteq> {}" using 1 2 assms by (metis Collect_mem_eq Sup_empty insert_compr insert_not_empty is_partition_of_def)
thus "X={{x}}" using 1 2 3 assms by (smt all_not_in_conv empty_subsetI in_mono insert_absorb2 insert_iff insert_mono insert_subset singleton_iff subsetI subset_antisym)
qed

lemma a5: fixes x shows "is_partition {{x}}" using is_partition_def by auto

lemma a6: fixes x shows "is_partition_of {{x}} {x}"
proof -
(* fix x
have "\<Union> {{x}} = {x}" by simp *)
show "is_partition_of {{x}} {x}" using a5 is_partition_of_def by fastforce
qed

lemma a4: fixes x X shows "is_partition_of X {x} = (X={{x}})" using a3 a6 by fast

(* compared to the above, the one below is an even more paper-like definition of "all partitions" *)
definition all_partitions_classical where "all_partitions_classical XX = 
{X . is_partition_of X XX}"

lemma a7: fixes x shows "all_partitions_classical {x} = {{{x}}}" (* using 
a1 a2 a3 all_partitions_classical_def *)
proof -
  have "all_partitions_classical {x} = {X . is_partition_of X {x}}" 
  using all_partitions_classical_def by blast
  also have "... = {X . X={{x}}}" using a4 by metis
  finally show ?thesis by force
qed
(*
lemma a8: fixes X Y assumes "is_partition Y" and "X \<subseteq> Y" shows "is_partition X"
proof -
{
fix x1
assume "x1 \<in> X" 
hence "x1 \<in> Y" using assms by blast
hence "x1 \<noteq> {} & (\<forall> x2 \<in> Y - {x1}. x1 \<inter> x2 = {})" using assms is_partition_def by (metis Diff_insert Diff_triv Int_def all_not_in_conv bot_set_def empty_iff inf_bot_right insert_Collect insert_compr)
hence "x1 \<noteq> {} & (\<forall> x2 \<in> X - {x1}. x1 \<inter> x2 = {})" using assms by blast
}
thus "is_partition X" using is_partition_def by metis
qed

lemma "{{1::nat}} \<in> allPartitions {1::nat}" (is "?P \<in> allPartitions ?A")
proof -
  def R \<equiv> "{(1::nat,1::nat)}"
  then have "equiv ?A R" unfolding equiv_def refl_on_def sym_def trans_def by fast
  moreover have "?A // R = ?P" unfolding R_def using partition_example .
  ultimately show "?thesis" unfolding allPartitions_def by auto
qed
*)

(* TODO CL: implement computable function
fun partition :: "'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a set" where
  "partition [] [] = {}" |
  "partition (x # xs) b = {}" |
  "partition a (x # xs) = {}"
*)

end
