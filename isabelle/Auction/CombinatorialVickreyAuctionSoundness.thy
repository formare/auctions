theory CombinatorialVickreyAuctionSoundness

imports "Sandbox/g"

begin

(* MC: left-totality for allocations *)
lemma assumes "winningAllocationRel N G t b \<in> winningAllocationsRel N G b"
shows "winningAllocationRel N G t b \<in> possibleAllocationsRel N G" using assms by force

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

lemma (*MC: each good gets allocated exactly once, and no other thing gets allocated *)
assumes "winningAllocationRel N G t b \<in> winningAllocationsRel N G b" shows
"Range (winningAllocationRel N G t b) partitions G"
using assms by (metis (hide_lams, no_types) lm03 lm47 set_rev_mp)

end

