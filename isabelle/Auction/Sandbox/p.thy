theory p
(* for testing stuff that should be added to ../Partitions.thy *)
imports "../Partitions"

begin

lemma
  assumes new: "B \<inter> A = {}"
      and non_empty: "B \<noteq> {}"
    (* TODO CL: assume something about f *)
  shows "\<forall> P . P partitions A \<longrightarrow>
    (\<exists> Q . Q partitions (A \<union> B)
      \<and> (\<Sum> X \<in> P . f X) \<le> (\<Sum> Y \<in> Q . f Y))"
proof (rule allImpI)
  fix P assume partA: "P partitions A"

  then have "(P \<union> {B}) partitions (A \<union> B) \<and> (\<forall> X \<in> P . \<exists> Y \<in> P \<union> {B} . X \<subseteq> Y)"
    using new non_empty
    by (rule exists_partition_of_strictly_larger_set)
  then have partB: "(P \<union> {B}) partitions (A \<union> B)"
        and sub: "\<forall> X \<in> P . \<exists> Y \<in> P \<union> {B} . X \<subseteq> Y" by simp_all

  have "(\<Sum> X \<in> P . f X) \<le> (\<Sum> Y \<in> P \<union> {B} . f Y)"
  proof -
    show ?thesis sorry
  qed
  with partB show "\<exists> Q . Q partitions (A \<union> B)
    \<and> (\<Sum> X \<in> P . f X) \<le> (\<Sum> Y \<in> Q . f Y)" by blast
qed

end
