theory CombinatorialVickreyAuctionSoundness

imports "Sandbox/g"

begin

term "Domain (Graph (\<lambda> b N G. winningAllocationRel N G t b))"

(* MC: left-totality for allocations *)
lemma assumes "winningAllocationRel N G t b \<in> winningAllocationsRel N G b"
shows "(\<exists> winningAllocationRel N G t b. True) & winningAllocationRel N G t b \<in> possibleAllocationsRel N G &
Domain (Graph (\<lambda> N G b. winningAllocationRel N G t b))=Domain (Graph (\<lambda> N G b. winningAllocationRel N G t b))" 
using assms by force

(* MC: price-nonnegativity & left-totality for prices *)
lemma fixes N::"participant set" fixes G::goods fixes b t n assumes
"EX i1 i2. i1 \<in> N - {i2} & i2 \<in> N - {i1} & 
(\<forall> t t'. (trivial t & trivial t' & Union t \<subseteq> Union t') \<longrightarrow>
setsum b ({i1}\<times>t) \<le> setsum b ({i1}\<times>t') & setsum b ({i2}\<times>t) \<le> setsum b ({i2}\<times>t'))"
"finite N"
"finite G"
"t (winningAllocationsRel N G b) \<in> winningAllocationsRel N G b"
shows "paymentsRel N G t b n \<ge> 0 & paymentsRel N G t b n \<in> Reals" using lm61e lm71 lm72b assms 
Reals_def by auto

(*MC: right-uniqueness *)
lemma "runiq (Graph (\<lambda> N. winningAllocationRel N G t b))" using l14b by fast
lemma "runiq (Graph (\<lambda> G. winningAllocationRel N G t b))" using l14b by fast
lemma "runiq (Graph (\<lambda> b. winningAllocationRel N G t b))" using l14b by fast
lemma "runiq (Graph (\<lambda> N. paymentsRel N G t b))" using l14b by fast
lemma "runiq (Graph (\<lambda> G. paymentsRel N G t b))" using l14b by fast
lemma "runiq (Graph (\<lambda> b. paymentsRel N G t b))" using l14b by fast

lemma lm81: (*MC: each good gets allocated exactly once, and no other thing gets allocated *)
assumes "winningAllocationRel N G t b \<in> winningAllocationsRel N G b" 
(*this is an assumption about t, not about b, G or N*)
shows "Range (winningAllocationRel N G t b) partitions G"
using assms by (metis (hide_lams, no_types) lm03 lm47 set_rev_mp)

term "winningAllocationsRel N G (b::altbids)"

lemma assumes "winningAllocationRel N G t b \<in> winningAllocationsRel N G b"
(*this is an assumption about t, not about b, G or N*)
"n1 \<in> N" "n2 \<in> N"
shows 
"
(* (G=(\<Union>n \<in> N. winningAllocationRel N G t b,,n)) 
*)

(winningAllocationRel N G t b),,n1 \<inter> 
((winningAllocationRel N G t b),,n2) = {}

"
using lm81 assms possible_allocations_rel_def injections_def all_partitions_def is_partition_of_def 
is_partition_def runiq_def sledgehammer

end

