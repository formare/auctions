(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Christoph Lange <math.semantic.web@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Sums of functions, that involve relations, over a set *}

theory SumsInvolvingRelations
imports
  RelationOperators
  
begin

lemma
  assumes "y \<notin> A"
  shows "(\<Sum> x \<in> A . f ((R \<union> {(y, z)}) ,, x)) = (\<Sum> x \<in> A . f (R ,, x))"
sorry

end

