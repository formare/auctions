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

header {* Additional material that we would have expected in Big_Operators.thy *}

theory Big_OperatorsUtils
imports
  CombinatorialVickreyAuction
  CombinatorialAuctionProperties
  
begin

lemma setsum_restrict_fun_zero:
  fixes A::"'a set"
    and S::"'a set"
    and f::"'a \<Rightarrow> 'b"
    and g::"'b \<Rightarrow> 'c\<Colon>{zero,comm_monoid_add}"
    and z::'b
  assumes finite: "finite S"
      and zero: "g z = 0"
  shows "(\<Sum> x \<in> S . g (if x \<in> A then f x else z)) = (\<Sum> x \<in> S \<inter> A . g (f x))"
(* TODO CL: Sledgehammer in Isabelle2013-1-RC2 doesn't find a proof given default timeout. *)
proof -
  have "(\<Sum> x \<in> S . g (if x \<in> A then f x else z)) = (\<Sum> x \<in> S . if x \<in> A then g (f x) else 0)"
    using zero by (metis (hide_lams, full_types))
  also have "\<dots> = (\<Sum> x \<in> S \<inter> A . g (f x))"
    using finite by (rule setsum_restrict_set[symmetric])
  finally show ?thesis .
qed

end

