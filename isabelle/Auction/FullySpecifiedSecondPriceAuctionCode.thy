(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Makarius Wenzel <wenzel@lri.fr>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* code generation setup for fully specified second price single good auction *}

theory FullySpecifiedSecondPriceAuctionCode
imports
  FullySpecifiedSecondPriceAuction
  "~~/src/HOL/Library/Code_Target_Numeral"

begin

code_include Scala ""
{*package code
*}
export_code fs_spa_winner fs_spa_allocation fs_spa_payments in Scala
(* In SML, OCaml and Scala "file" is a file name; in Haskell it's a directory name ending with / *)
module_name Vickrey file "code/generated/code.scala"
(* A trivial example to try interactively with the generated Scala code:

:load code.scala
Vickrey.times_int(Vickrey.Zero_int(), Vickrey.Zero_int())

Notes:
* There are apparently no ready-to-use code-unfold theorems (codegen \<section>2.2) in the library.
*)
(*
print_codeproc
*)

end
