theory a
imports Main
  Partitions
begin


lemma partition_contains_subsets:
  fixes A P
  assumes "is_partition_of P A"
  shows "P \<subseteq> Pow A"
proof -
  have "P \<subseteq> Pow (\<Union> P)" by fast
  with assms show "P \<subseteq> Pow A" using is_partition_of_def by metis
qed

lemma Pow_example: "Pow {x} = {{},{x}}" by fast (* CL@MC: no sledgehammering required *)

lemma partition_of_singleton:
  fixes x A
  assumes "is_partition_of A {x}"
  shows "A={{x}}"
proof -
  have 1: "A \<subseteq> {{},{x}}" using partition_contains_subsets Pow_example assms by blast
  moreover have 2: "\<not> {} \<in> A" using is_partition_def assms is_partition_of_def by metis
  moreover have 3: "A \<noteq> {}" using assms by (metis Sup_empty insert_not_empty is_partition_of_def)
  ultimately show "A={{x}}" using assms by (smt all_not_in_conv empty_subsetI in_mono insert_absorb2 insert_iff insert_mono insert_subset singleton_iff subsetI subset_antisym)
qed

lemma a5: fixes x shows "is_partition {{x}}" using is_partition_def by auto

lemma a6: fixes x shows "is_partition_of {{x}} {x}"
proof -
(* fix x
have "\<Union> {{x}} = {x}" by simp *)
show "is_partition_of {{x}} {x}" using a5 is_partition_of_def by fastforce
qed

lemma a4: fixes x X shows "is_partition_of X {x} = (X={{x}})" using partition_of_singleton a6 by fast

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