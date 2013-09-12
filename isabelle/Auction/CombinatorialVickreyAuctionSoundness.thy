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

text {* The combinatorial Vickrey auction in relational form is left-total.
  Note that in Isabelle/HOL's logic of total functions, an outcome (allocation @{term x} and
  @{term p}) will always trivially exist, as they are return values of functions.  It is more
  interesting to prove that the outcome of our auction is \emph{well-defined}. *}
lemma left_total:
  fixes t::tie_breaker_rel
  shows "left_total (nVCG_auctions t) admissible_input"
proof (rule left_totalI)
  fix G::goods and N::"participant set" and b::bids
  assume assm: "admissible_input G N b"
  def x \<equiv> "winning_allocation_rel G N t b"
  def p \<equiv> "payments_rel G N t b"
  from assm x_def p_def have "nVCG_pred t G N b x p" unfolding nVCG_pred_def by blast
  then show "\<exists> x p . ((G, N, b), (x, p)) \<in> nVCG_auctions t"
    unfolding nVCG_auctions_def using pred_imp_rel_all by metis
qed

text {* The combinatorial Vickrey auction in relational form is right-unique.  This is easy to 
  show because its outcome is defined by two functions, which are right-unique by construction. *}
lemma right_unique:
  fixes t::tie_breaker_rel
  shows "right_unique (nVCG_auctions t) admissible_input"
proof (rule right_uniqueI)
  fix G::goods and N::"participant set" and b::bids
  assume admissible: "admissible_input G N b"
  fix x::allocation_rel and x'::allocation_rel and p::payments and p'::payments

  have *: "\<And> G' N' b' x'' p'' . ((G', N', b'), (x'', p'')) \<in> (nVCG_auctions t) \<Longrightarrow>
    x'' = winning_allocation_rel G' N' t b' \<and> p'' = payments_rel G' N' t b'"
  proof -
    fix G' N' b' x'' p''
    assume "((G', N', b'), (x'', p'')) \<in> (nVCG_auctions t)"
    then have "pred_tup (nVCG_pred t) ((G', N', b'), (x'', p''))"
      unfolding nVCG_auctions_def rel_all_def by fast
    then show "x'' = winning_allocation_rel G' N' t b' \<and> p'' = payments_rel G' N' t b'"
      unfolding pred_tup_def nVCG_pred_def by blast
  qed

  assume "((G, N, b), (x, p)) \<in> (nVCG_auctions t)"
  then have xp: "x = winning_allocation_rel G N t b \<and> p = payments_rel G N t b" by (rule *)
    
  assume "((G, N, b), (x', p')) \<in> (nVCG_auctions t)"
  then have xp': "x' = winning_allocation_rel G N t b \<and> p' = payments_rel G N t b" by (rule *)

  from xp xp' show "x = x' \<and> p = p'" by fast
qed

end

