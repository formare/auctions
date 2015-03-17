(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>


Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Definitions about those Combinatorial Auctions which are strict (i.e., which assign all the available goods) *}

theory StrictCombinatorialAuction
imports Complex_Main
  Partitions
  MiscTools

begin

section {* Types *}

type_synonym index = "integer"
type_synonym participant = index
type_synonym good = nat
type_synonym goods = "good set"
type_synonym price = real
type_synonym bids3 = "((participant \<times> goods) \<times> price) set"
type_synonym bids = "participant \<Rightarrow> goods \<Rightarrow> price"
type_synonym allocation_rel = "(goods \<times> participant) set"
type_synonym allocation = "(participant \<times> goods) set" 
type_synonym payments = "participant \<Rightarrow> price"
type_synonym bidvector = "(participant \<times> goods) \<Rightarrow> price"
abbreviation "bidvector (b::bids) == split b"
abbreviation "proceeds (b::bidvector) (allo::allocation) == setsum b allo"
abbreviation "winnersOfAllo (a::allocation) == Domain a"
abbreviation "allocatedGoods (allo::allocation) == \<Union> (Range allo)"

(* possible_allocations_rel defines all possible allocations of a set of goods G to a set of participants N: 
  injective functions that map sets of goods to their potential buyers, i.e.\ participants.
  Here, we assume that everything gets allocated, i.e. that there is no free disposal.
  This assumption facilitates the paper\<leftrightarrow>algorithm equivalence proof for injective functions.
*)
fun possible_allocations_rel 
  where "possible_allocations_rel G N = Union { injections Y N | Y . Y \<in> all_partitions G }" 

(* The following abbreviations duplicate the corresponding definitions in RelationProperties.thy. This is done since typically abbreviations are efficient in theorem proving, however, not in code extraction. *)

abbreviation "is_partition_of' P A == (\<Union> P = A \<and> is_non_overlapping P)"
abbreviation "all_partitions' A == {P . is_partition_of' P A}"
abbreviation "injections' X Y == {R . Domain R = X \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"
abbreviation "possible_allocations_rel' G N == Union{injections' Y N | Y . Y \<in> all_partitions' G}"
abbreviation possibleAllocationsRel where 
  "possibleAllocationsRel N G == converse ` (possible_allocations_rel G N)"

text {* algorithmic version of @{const possible_allocations_rel} *}
fun possible_allocations_alg :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel list"
  where "possible_allocations_alg G N = 
         concat [ injections_alg Y N . Y \<leftarrow> all_partitions_alg G ]"

abbreviation "possibleAllocationsAlg N G == 
              map converse (concat [(injections_alg l N) . l \<leftarrow> all_partitions_list G])"



section {* VCG mechanism *}

(* N is the set of bidders, G the set of goods, and b the bidvector *)
abbreviation "winningAllocationsRel N G b == 
              argmax (setsum b) (possibleAllocationsRel N G)"

(* t is a tie breaking function *)
abbreviation "winningAllocationRel N G t b == t (winningAllocationsRel N G b)"

(* This is the computational version of winningAllocationsRel *)
abbreviation "winningAllocationsAlg N G b == argmaxList (proceeds b) (possibleAllocationsAlg N G)"

(* This is the computational version of winningAllocationRel *)
definition "winningAllocationAlg N G t b == t (winningAllocationsAlg N G b)"

text {* payments *}

text {* alpha is the maximum sum of bids of all bidders except bidder @{text n}'s bid, computed over all possible allocations of all goods,
  i.e. the value reportedly generated by value maximization when solved without n's bids *}
abbreviation "alpha N G b n == Max ((setsum b)`(possibleAllocationsRel (N-{n}) G))"

(* computational version of alpha *)
abbreviation "alphaAlg N G b n == Max ((proceeds b)`(set (possibleAllocationsAlg (N-{n}) (G::_ list))))"

(* revenue with participant n removed from winning allocation *)
abbreviation "remainingValueRel N G t b n == setsum b ((winningAllocationRel N G t b) -- n)"

(* computational version of remainingValueRel *)
abbreviation "remainingValueAlg N G t b n == proceeds b ((winningAllocationAlg N G t b) -- n)"

(* function to determine payments for each participant *)
abbreviation "paymentsRel N G t == (alpha N G) - (remainingValueRel N G t)"

(* computational version of paymentsRel *)
definition "paymentsAlg N G t == (alphaAlg N G) - (remainingValueAlg N G t)"

end

