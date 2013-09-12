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

(* TODO CL: While this is the same as what we did for single good Vickrey, it's not completely
   satisfying: In Isabelle/HOL's logic of total functions, x and p will always trivially exist,
   but we want to know whether, for any concrete input, there is a concrete outcome.
   (Not sure what's the right terminology.) *)
lemma left_total:
  fixes t::tie_breaker_rel
  shows "left_total (nVCG_auctions t) admissible_input"
proof (rule left_totalI)
  fix G::goods and N::"participant set" and b::bids
  assume assm: "admissible_input G N b"
  (* TODO CL: We may need the following to really prove definedness of the outcome
  {
    fix n::participant
    fix H::goods
    assume "n \<in> N \<and> H \<subseteq> G"
    with assm have "b n H \<in> Prices" unfolding admissible_input_def by metis
  }
  *)
  def x \<equiv> "winning_allocation_rel G N t b"
  def p \<equiv> "payments_rel G N t b"
  from assm x_def p_def have "nVCG_pred t G N b x p" unfolding nVCG_pred_def by blast
  then show "\<exists> x p . ((G, N, b), (x, p)) \<in> nVCG_auctions t"
    unfolding nVCG_auctions_def using pred_imp_rel_all by metis
qed

end

