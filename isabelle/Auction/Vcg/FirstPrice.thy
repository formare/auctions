
abbreviation "firstPriceP N \<Omega> b r n ==
  b (n, winningAllocationAlg N \<Omega> r b,, n)"

lemma assumes "\<forall> X. b (n, X) \<ge> 0" shows
"firstPriceP N \<Omega> b r n \<ge> 0" using assms by blast

