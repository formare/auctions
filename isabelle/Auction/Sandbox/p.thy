theory p
(* for testing stuff that should be added to ../Partitions.thy *)
imports "../Partitions"
  "../RelationProperties"

begin

lemma foo:
  assumes "\<forall> x \<in> A . (\<exists>! y \<in> B . p x y)"
  obtains f where "f ` A \<subseteq> B"
proof
  let ?f = "\<lambda> x . (if x \<in> A then THE y . y \<in> B \<and> p x y else undefined)"
  show "?f ` A \<subseteq> B"
  proof
    fix y assume "y \<in> ?f ` A"
    then have "\<exists> x \<in> A . y = (THE y . y \<in> B \<and> p x y)" by (smt imageE)
    then have "\<exists> x \<in> A . y = ?f x" by metis
    with assms show "y \<in> B" by (smt theI)
  qed
qed

lemma
  fixes A::"'a::{ordered_ab_semigroup_add,comm_monoid_add} set"
    and B::"'a::{ordered_ab_semigroup_add,comm_monoid_add} set"
  assumes finiteA: "finite A"
      and finiteB: "finite B"
      and pp: "p x y \<Longrightarrow> f x \<le> f y"
      and exU: "\<forall> x \<in> A . (\<exists>! y \<in> B . p x y)"
      and non_neg: "\<forall> x . f x \<ge> (0::'a::{ordered_ab_semigroup_add,comm_monoid_add})" (* TODO CL: maybe need to restrict x to some set *)
  shows "(\<Sum> x \<in> A . f x) \<le> (\<Sum> y \<in> B . f y)"
proof -
  from exU obtain g where "g ` A \<subseteq> B" by (rule foo)
  then have "B = g ` A \<union> (B - g ` A)" by fast
  moreover have "g ` A \<inter> (B - g ` A) = {}" by simp
  ultimately have "(\<Sum> y \<in> B . f y) = (\<Sum> y \<in> g ` A . f y) + (\<Sum> y \<in> B - g ` A . f y)" using finiteA finiteB
    by (metis finite_Un setsum.union_disjoint)
  also have "\<dots> \<ge> (\<Sum> y \<in> g ` A . f y)"
  proof -
    have "\<forall> y \<in> B - g ` A . f y \<ge> (0::'a::{ordered_ab_semigroup_add,comm_monoid_add})" using non_neg by fast
    then have "(\<Sum> y \<in> B - g ` A . f y) \<ge> 0" by (rule setsum_nonneg)
    then show ?thesis by (metis add_left_mono monoid_add_class.add.right_neutral)
  qed
oops

lemma
  assumes finite: "finite A"
      and new: "B \<inter> A = {}"
      and non_empty: "B \<noteq> {}"
      and f_non_neg: "\<forall> x . f x \<ge> (0::'a::{comm_monoid_add, ordered_ab_semigroup_add})"
    (* TODO CL: assume something about f, e.g. monotonicity wrt. subsets *)
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
    from f_non_neg have "(\<Sum> X \<in> P . f X) \<le> (\<Sum> X \<in> P . f X) + f B"
        by (metis add_left_mono comm_monoid_add_class.add.right_neutral)
    also have "\<dots> = (\<Sum> X \<in> P \<union> {B} . f X)"
    proof -
      have "finite P" using finite partA unfolding is_partition_of_def by (metis finite_UnionD)
      moreover have "finite {B}" by simp
      moreover have "P \<inter> {B} = {}" using partA new
        by (metis Int_insert_right_if0 Set.set_insert Sup_insert inf_bot_right inf_sup_absorb is_partition_of_def non_empty)
      ultimately have "setsum f (P \<union> {B}) = setsum f P + setsum f {B}" by (rule setsum.union_disjoint)
      then show ?thesis by force
    qed
    finally show ?thesis by fast
  qed
  with partB show "\<exists> Q . Q partitions (A \<union> B)
    \<and> (\<Sum> X \<in> P . f X) \<le> (\<Sum> Y \<in> Q . f Y)" by blast
qed

end
