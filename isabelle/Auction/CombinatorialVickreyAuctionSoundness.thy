(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Soundness verification of the combinatorial Vickrey auction *}

theory CombinatorialVickreyAuctionSoundness
imports
  CombinatorialVickreyAuction
  CombinatorialAuctionProperties
  
begin

lemma left_total:
  shows "left_total (nVCG_auctions t) admissible_input"
unfolding left_total_def
proof
  fix x
  (* assuming anything about x won't help, as admissible_input \<equiv> True *)
  (* TODO CL: admissible_input needs fixing, maybe using FuncSet *)
  show "x \<in> Domain (nVCG_auctions t)" unfolding nVCG_auctions_def admissible_input_def sorry
qed

end

