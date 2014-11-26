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

header {* Combinatorial Auctions (examples for testing) *}

theory CombinatorialAuctionTest
imports
  CombinatorialAuction
begin

section {* the example from ``The Lovely but Lonely Vickrey Auction'' *}

definition paper_example_participants :: "participant set" where "paper_example_participants = {1::nat, 2, 3}"
definition paper_example_goods :: goods where "paper_example_goods = {(* A *) 11, (* B *) 12}"
definition paper_example_bids :: bids where "paper_example_bids bidder goods = (
      if (bidder = 1 \<and> goods = {11,12}
          \<or> (bidder = 2 \<or> bidder = 3) \<and> card goods = 1)
      then 2
      else 0)"
definition paper_example_allocation :: allocation_rel
where "paper_example_allocation = {({12}, 2), ({11}, 3)}"

section {* the same (?) as above, in CATS format with dummy bids *}

definition cats_example_participants :: "participant set" where "cats_example_participants = {0..4}"
definition cats_example_goods :: goods where "cats_example_goods = {0..3}"
definition cats_example_bids :: bids where "cats_example_bids bidder goods = (
      if (
          bidder = 0 \<and> goods = {0,1}
        \<or> bidder = 1 \<and> goods = {0,2}
        \<or> bidder = 2 \<and> goods = {1,2}
        \<or> bidder = 3 \<and> goods = {0,3}
        \<or> bidder = 4 \<and> goods = {1,3}
      ) then 2
      else 0)"

section {* single-good auction as a special case of a combinatorial auction *}

definition sga_goods :: goods where "sga_goods = {1::nat}"
definition sga_bids :: "(participant \<Rightarrow> price) \<Rightarrow> bids"
where "sga_bids b = (\<lambda> bidder goods . (
      if goods = sga_goods then b bidder else 0))"

end

