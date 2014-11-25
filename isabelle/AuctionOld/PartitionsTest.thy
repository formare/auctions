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

theory PartitionsTest
imports Partitions
  "~~/src/HOL/Library/Code_Target_Nat"

begin

lemma "is_partition {{1::nat}}" unfolding is_partition_def try
by fastforce

end
