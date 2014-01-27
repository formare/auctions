theory p
(* for testing stuff that should be added to ../Partitions.thy *)
imports "../Partitions"

begin

lemma
  assumes new: "B \<inter> A = {}"
      and non_emptyA: "A \<noteq> {}"
      and non_emptyB: "B \<noteq> {}"
    (* TODO CL: assume something about f *)
  shows "\<forall> P . P partitions A \<longrightarrow>
    (\<exists> Q . Q partitions (A \<union> B)
      \<and> (\<Sum> X \<in> P . f X) \<le> (\<Sum> Y \<in> Q . f Y))"
proof
  fix P assume part: "P partitions A"
oops

  (*
  shows "\<exists> Q . Q partitions (A \<union> B) \<and> (\<forall> X \<in> P . \<exists> Y \<in> Q . X \<subseteq> Y)"
  *)
end
