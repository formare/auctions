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

header {* code generation setup for combinatorial Vickrey auction *}

theory CombinatorialVickreyAuctionCode
imports CombinatorialVickreyAuction
  "~~/src/HOL/Library/Code_Target_Numeral"
begin

code_printing code_module "" => (Scala) {*package CombinatorialVickreyAuction*} 

export_code winning_allocations_alg_CL payments_alg in Scala
(* In SML, OCaml and Scala "file" is a file name; in Haskell it's a directory name ending with / *)
file "code/generated/CombinatorialVickreyAuction.scala"

end

