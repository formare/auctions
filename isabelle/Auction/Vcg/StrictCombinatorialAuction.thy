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

type_synonym index = "nat"
type_synonym participant = index
type_synonym good = nat
type_synonym goods = "nat set" (* CL: actually we'd prefer "'a set", as we really don't care about the type *)
type_synonym price = real

(*
CL: Keeping old initial vector-based bid implementation (suitable for multiple items per good and
  fractions of items) for reference.
		
(* one participant's bid on a set of goods *)
definition b :: "participant \<Rightarrow> goods \<Rightarrow> nat" where "b i y = (\<Sum> x \<in> y . x)"

text{* convenience type synonyms for most of the basic concepts we are dealing with *}
type_synonym endowment = "nat vector" (* conceptually: good \<Rightarrow> quantity *)
type_synonym endowment_subset = "nat vector" (* conceptually the same, but \<le> endowment *)

(* A single participant ascribes real values to subsets of the endowment. *)
type_synonym valuation = "endowment_subset \<Rightarrow> real"
type_synonym valuations = "valuation vector"
type_synonym bid = "endowment_subset \<Rightarrow> real"

(* A well-formed bid is non-negative for each “subset” of the endowment, i.e. each vector s
   that is component-wise 0 \<le> s \<le> x0. *)
definition bid :: "bid \<Rightarrow> goods \<Rightarrow> endowment \<Rightarrow> bool"
  where "bid b K x0 \<longleftrightarrow> (\<forall> s . non_negative_real_vector K s \<and> vector_le K s x0 \<longrightarrow> b s \<ge> 0)"

type_synonym allocation = "participant \<Rightarrow> endowment_subset"

type_synonym payments = "real vector"
*)

type_synonym bids3 = "((participant \<times> goods) \<times> price) set"
type_synonym bids = "participant \<Rightarrow> goods \<Rightarrow> price"
type_synonym allocation_rel = "(goods \<times> participant) set"
type_synonym allocation = "(participant \<times> goods) set"
(* CL: providing a separate "goods set", as for allocation_fun below, is not necessary,
   since the function-as-relation-as-set representation already includes the domain
   on which we intend the function to work :-)  When representing the allocation as a function,
   we do need the set on which we intend to use the function, as Isabelle's functions are
   always total. *)

type_synonym payments = "participant \<Rightarrow> price"
type_synonym altbids = "(participant \<times> goods) \<Rightarrow> price"
type_synonym bidvector=altbids
abbreviation "altbids (b::bids) == split b"
(* CL: I don't understand the choice of the name "proceeds". *)
abbreviation "proceeds (b::altbids) (allo::allocation) == setsum b allo"

abbreviation participants where "participants (a::allocation) == Domain a"
abbreviation goods::"allocation => goods" where "goods (allo::allocation) == \<Union> (Range allo)"

(*
text {* all possible allocations of a set of goods to a set of participants: 
  injective functions that map sets of goods to their potential buyers, i.e.\ participants.
  Here, we assume that everything gets allocated, i.e. that there is no free disposal.
  This assumption facilitates the paper\<leftrightarrow>algorithm equivalence proof for injective functions. *}
*)
fun possible_allocations_rel 
where "possible_allocations_rel G N = Union { injections Y N | Y . Y \<in> all_partitions G }" 

abbreviation "is_partition_of' P A == (\<Union> P = A \<and> is_partition P)"

abbreviation "all_partitions' A == {P . is_partition_of' P A}"

abbreviation "injections' X Y == {R . Domain R = X \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"

abbreviation "possible_allocations_rel' G N == Union{injections' Y N | Y . Y \<in> all_partitions' G}"

abbreviation possibleAllocationsRel where 
"possibleAllocationsRel N G == converse ` (possible_allocations_rel G N)"

notepad
begin
  fix Rs::"('a \<times> 'b) set set"
  fix Sss::"'a set set"
  fix P::"'a set \<Rightarrow> ('a \<times> 'b) set set"
  (* TODO CL: an example (to be mentioned in the paper) for how hard set theory is for Isabelle:
     takes several minutes to find (2013), 104 ms to prove 
     MC: substituted smt with blast in view of afp submission; however, I think CL's comment above still applies. *)
  have "{ R . \<exists> Y \<in> Sss . R \<in> P Y } = \<Union> { P Y | Y . Y \<in> Sss }" 
  using Collect_cong Union_eq mem_Collect_eq by blast
end

text {* algorithmic version of @{const possible_allocations_rel} *}
fun possible_allocations_alg :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel list"
where "possible_allocations_alg G N = 
concat [ injections_alg Y N . Y \<leftarrow> all_partitions_alg G ]"
abbreviation "possibleAllocationsAlg N G == 
(map converse (possible_allocations_alg G N))"
abbreviation "possibleAllocationsAlg2 N G == 
converse ` (\<Union> set [set (injections_alg l N) . l \<leftarrow> all_partitions_list G])"
abbreviation "possibleAllocationsAlg3 N G == 
map converse (concat [(injections_alg l N) . l \<leftarrow> all_partitions_list G])"
lemma lm01: "set (possibleAllocationsAlg3 N G) = possibleAllocationsAlg2 N G"
using assms by auto

(* example (uncomment to run): possibilities to allocate goods {1,2,3} to participants {100,200} *)
(*
value "possible_allocations_alg {1,2,3::nat} {100,200::nat}"
value "map converse (possible_allocations_alg {1,2,3::nat} {100,200::nat})"
value "possibleAllocationsAlg {100,200::nat} {1,2,3::nat}"
*)

section {* VCG mechanism *}

abbreviation "winningAllocationsRel N G b == 
argmax (setsum b) (possibleAllocationsRel N G)"

abbreviation "winningAllocationRel N G t b == t (winningAllocationsRel N G b)"

abbreviation "winningAllocationsAlg N G b == argmaxList (proceeds b) (possibleAllocationsAlg3 N G)"

definition "winningAllocationAlg N G t b == t (winningAllocationsAlg N G b)"

text {* payments *}

text {* the maximum sum of bids of all bidders except bidder @{text n}'s bid, computed over all possible allocations of all goods,
  i.e. the value reportedly generated by value maximization problem when solved without n's bids *}

abbreviation "alpha N G b n == Max ((setsum b)`(possibleAllocationsRel (N-{n}) G))"

abbreviation "remainingValueRel N G t b n == setsum b (winningAllocationRel N G t b -- n)"

abbreviation "paymentsRel N G t == alpha N G - remainingValueRel N G t"

abbreviation "remainingValueAlg N G t b n == proceeds b (winningAllocationAlg N G t b -- n)"

abbreviation "alphaAlg N G b n == Max ((proceeds b)`(set (possibleAllocationsAlg3 (N-{n}) (G::_ list))))"
definition "paymentsAlg N G t == alphaAlg N G - remainingValueAlg N G t"

section {* Uniform tie breaking: definitions *}
text{* To each allocation we associate the bid in which each participant bids for a set of goods 
the cardinality of the intersection of that set with the set she gets in the given allocation.
By construction, the revenue of an auction run using this bid is maximal on the given allocation,
and this maximal is unique.
We can then use the bid constructed this way @{term tiebids'} to break ties by running an auction 
having the same form as a normal auction (that is why we use the adjective ``uniform''), 
only with this special bid vector. *}
abbreviation "omega pair == {fst pair} \<times> (finestpart (snd pair))"
abbreviation "pseudoAllocation allocation == \<Union> (omega ` allocation)"
(*abbreviation "allocation2Goods allocation == \<Union> (snd ` allocation)"*)
abbreviation "bidMaximizedBy allocation N G == 
(* (N \<times> finestpart G) \<times> {0::price} +* ((pseudoAllocation allocation) \<times> {1}) *)
pseudoAllocation allocation <|| ((N \<times> (finestpart G)))"
abbreviation "maxbid' a N G == toFunction (bidMaximizedBy a N G)"
abbreviation "partialCompletionOf bids pair == (pair, setsum (%g. bids (fst pair, g)) (finestpart (snd pair)))"
abbreviation "test bids pair == setsum (%g. bids (fst pair, g)) (finestpart (snd pair))"
abbreviation "LinearCompletion bids N G == (partialCompletionOf bids) ` (N \<times> (Pow G - {{}}))"
abbreviation "linearCompletion' bids N G == toFunction (LinearCompletion bids N G)"
abbreviation "tiebids' a N G == linearCompletion' (maxbid' a N G) N G"
abbreviation "Tiebids a N G == LinearCompletion (real\<circ>maxbid' a N G) N G"
abbreviation "chosenAllocation' N G bids random == 
hd(perm2 (takeAll (%x. x\<in>(winningAllocationsRel N (set G) bids)) (possibleAllocationsAlg3 N G)) random)"
abbreviation "resolvingBid' N G bids random == tiebids' (chosenAllocation' N G bids random) N (set G)"

end

