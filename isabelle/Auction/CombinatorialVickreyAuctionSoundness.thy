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
  fixes t::tie_breaker_rel
  shows "left_total (nVCG_auctions t) admissible_input"
proof (rule left_totalI)
  fix G::goods and N::"participant set" and b::bids
  assume "admissible_input G N b"
  show "\<exists> x p . ((G, N, b), (x, p)) \<in> nVCG_auctions t" sorry
qed

end

