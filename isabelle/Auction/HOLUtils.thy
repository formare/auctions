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

header {* Additional material that we would have expected in HOL.thy *}

theory HOLUtils
imports
  HOL
begin

text {* An inference rule that combines @{thm allI} and @{thm impI} to a single step *}
lemma allImpI: "(\<And> x . p x \<Longrightarrow> q x) \<Longrightarrow> \<forall> x . p x \<longrightarrow> q x" by simp

end
