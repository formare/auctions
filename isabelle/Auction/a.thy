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
  shows "A = {{x}}"
proof -
  from assms have "A \<subseteq> {{},{x}}" using partition_contains_subsets Pow_example by blast
  moreover have "\<not> {} \<in> A" using assms unfolding is_partition_def is_partition_of_def by fast
  moreover have "A \<noteq> {}" using assms by (metis Sup_empty insert_not_empty is_partition_of_def)
  ultimately show "A = {{x}}" using assms by (metis subset_insert_iff subset_singletonD)
qed

lemma singleton_partition_ex1: "is_partition {{x}}" unfolding is_partition_def by fast

lemma singleton_partition_ex2: "is_partition_of {{x}} {x}"
using singleton_partition_ex1 is_partition_of_def by fastforce

lemma singleton_partition_ex3: "is_partition_of X {x} \<longleftrightarrow> (X = {{x}})"
using partition_of_singleton singleton_partition_ex2 by fast

lemma all_partitions_of_singleton: "all_partitions_classical {x} = {{{x}}}"
proof -
  have "all_partitions_classical {x} = {X . is_partition_of X {x}}" 
    using all_partitions_classical_def .
  also have "\<dots> = {X . X={{x}}}" using singleton_partition_ex3 by metis
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

end
