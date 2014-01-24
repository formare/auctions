theory p

imports "../Partitions"

begin

value "all_partitions_alg {1::nat}"
term "all_partitions {1::nat}"

lemma assumes "x \<in> all_partitions X" shows 
"EX y. y \<in> all_partitions (X \<union> Y) \<and> x \<subseteq> y'"
proof -
show ?thesis sorry
qed

end

