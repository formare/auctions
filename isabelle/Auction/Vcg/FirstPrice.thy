(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* VCG auction: definitions and theorems *}

theory FirstPrice

imports
CombinatorialAuction
    
(* The following three theories are needed for the extraction of Scala code *)
"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int" 
"~~/src/HOL/Library/Code_Numeral"

begin
abbreviation "firstPriceP N \<Omega> b r n ==
  b (n, winningAllocationAlg N \<Omega> r b,, n)"

lemma assumes "\<forall> X. b (n, X) \<ge> 0" shows
"firstPriceP N \<Omega> b r n \<ge> 0" using assms by blast
end

