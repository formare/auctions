(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Marco B. Caminati http://caminati.co.nr

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* soundness verification of combinatorial Vickrey auction *}

theory CombinatorialVickreyAuctionTest
imports
  CombinatorialAuctionTest
  CombinatorialVickreyAuction
  "~~/src/HOL/Library/Code_Target_Nat"

begin

value "max_revenue_alg paper_example_goods paper_example_participants paper_example_bids"
value "max_revenue_alg cats_example_goods cats_example_participants cats_example_bids"

value "winning_allocations_alg_CL
  paper_example_goods
  paper_example_participants
  paper_example_bids"

value "winning_allocations_alg_CL
  cats_example_goods
  cats_example_participants
  cats_example_bids"

(*
value "winning_allocations_alg_MC 
  paper_example_goods
  paper_example_participants
  paper_example_bids"
*)

value "{(n, payments_alg paper_example_goods paper_example_participants hd paper_example_bids n) | n . n \<in> paper_example_participants}"
value "{(n, \<alpha>_alg paper_example_goods paper_example_participants paper_example_bids n) | n . n \<in> paper_example_participants}"

value "{(n, payments_alg cats_example_goods cats_example_participants hd cats_example_bids n) | n . n \<in> cats_example_participants}"
value "{(n, \<alpha>_alg cats_example_goods cats_example_participants cats_example_bids n) | n . n \<in> cats_example_participants}"

value "hd (winning_allocations_alg_CL
  sga_goods
  {0::nat, 1, 2}
  (sga_bids (nth [23::nat, 42, 31]))
)"
value "{(x, payments_alg sga_goods {0::nat, 1, 2} hd (sga_bids (nth [23::nat, 42, 31])) x) | x . x \<in> {0::nat, 1, 2}}"

section {* a case where it is optimal not to allocate a good *}

definition partial_alloc_participants where "partial_alloc_participants = {1::nat, 2}"
definition partial_alloc_goods where "partial_alloc_goods = {(* A *) 98::nat, (* B *) 99}"
definition partial_alloc_bids where "partial_alloc_bids bidder goods = (
      if (bidder = 1 \<and> goods = {98}) then 200
      else if (bidder = 2 \<and> goods = {98,99}) then 100
      else 0)"

value "winning_allocations_alg_CL
  partial_alloc_goods
  partial_alloc_participants
  partial_alloc_bids"

value "possible_allocations_alg
  partial_alloc_goods
  partial_alloc_participants"

end

