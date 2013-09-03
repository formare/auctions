(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Christoph Lange <math.semantic.web@gmail.com>
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory PartitionsTest
imports Partitions
begin

(* partition of a set w.r.t. an equivalence relation: *)
value "{1::nat} // {(1::nat,1::nat)}"

(* testing a concrete partition, this time not with "value" *)
lemma partition_example: "{1::nat} // {(1::nat,1::nat)} = {{1::nat}}" (is "?lhs = ?rhs")
proof (rule equalitySubsetI)
  fix x assume "x \<in> ?lhs"
  then have "x \<in> {{(1::nat, 1)} `` {1::nat}}" by (metis singleton_quotient)
  then show "x \<in> ?rhs" by auto
next
  fix x assume "x \<in> ?rhs"
  then have "x \<in> {{(1::nat, 1)} `` {1::nat}}" by fast
  then show "x \<in> ?lhs" by (metis singleton_quotient)
qed
  
(* This is really an equivalence relation. *)
lemma "equiv {1::nat} {(1::nat,1::nat)}" unfolding equiv_def refl_on_def sym_def trans_def by fast

(* This should work (returning {(1::nat,1::nat)}) but doesn't.
   Seems we really need a recursive function that enumerates
   all equivalence relations over a set (or even directly all partitions of the set). *)
(* This list post seems related: https://groups.google.com/d/msg/fa.isabelle/SwVl-K3bvFs/DKyQDrE917gJ *)
(*
value "{R \<in> {{(1::nat,1::nat)}} . equiv {1::nat} R}"
*)

(* example using the list representation *)
value "all_partitions_list [1::nat,2,3]"

(* example using the set representation *)
value "all_partitions_alg {1::nat,2,3,4}"

(* testing allPartitions *)
lemma "{{1::nat}} \<in> all_partitions_wrt_equiv {1::nat}" (is "?P \<in> all_partitions_wrt_equiv ?A")
proof -
  def R \<equiv> "{(1::nat,1::nat)}"
  then have "equiv ?A R" unfolding equiv_def refl_on_def sym_def trans_def by fast
  moreover have "?A // R = ?P" unfolding R_def using partition_example .
  ultimately show "?thesis" unfolding all_partitions_wrt_equiv_def by auto
qed

end
