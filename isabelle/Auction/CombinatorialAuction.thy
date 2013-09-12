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

header {* Combinatorial Auctions *}

theory CombinatorialAuction
imports Complex_Main
  Vectors
  Partitions
  RelationProperties
  "~~/src/HOL/Library/FuncSet"

begin

section {* Types *}

type_synonym participant = index
type_synonym goods = "nat set" (* CL: actually we'd prefer "'a set", as we really don't care about the type *)
type_synonym price = real
definition Prices where "Prices = \<real>"

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

type_synonym bids = "participant \<Rightarrow> goods \<Rightarrow> price"
type_synonym allocation_rel = "((goods \<times> participant) set)" (* CL: goods set not necessary as the function-as-relation-as-set representation carries its own domain :-) *)
type_synonym tie_breaker_rel = "allocation_rel set \<Rightarrow> allocation_rel"
type_synonym tie_breaker_alg = "allocation_rel list \<Rightarrow> allocation_rel"
type_synonym payments = "participant \<Rightarrow> price"

(* CL: probably not needed, neither for close-to-paper nor for computable version
type_synonym allocation_fun = "(goods set) \<times> (goods \<rightharpoonup> participant)"
type_synonym tie_breaker_fun = "allocation_fun set \<Rightarrow> allocation_fun"
*)

type_synonym combinatorial_auction = "((goods \<times> participant set \<times> bids) \<times> (allocation_rel \<times> payments)) set"

section {* Admissible input *}

type_synonym input_admissibility = "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> bool"

text {* Admissible input (i.e.\ admissible bids, given the goods and participants).  As we represent
  @{typ bids} as functions, which are always total in Isabelle/HOL, we can't simply test, e.g., whether
  their domain is @{term "G \<times> N"} for the given goods @{term G} and participants @{term N}.  Therefore
  we test whether the function returns a value within some set. *}
(* CL: Once we realise general/special auctions using locales, we need an admissible_input axiom. *)
definition admissible_input :: "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> bool"
where "admissible_input G N b = (\<forall> n H . n \<in> N \<and> H \<subseteq> G \<longrightarrow> b n H \<in> Prices)"

section {* Tie breakers *}

text {* break ties by preferring an arbitrary existing allocation
  (we omit type annotations to keep this function polymorphic, so that we can use it with 
   both relational and functional allocations) *}
definition tie_breaker_example :: tie_breaker_rel where "tie_breaker_example x = (THE y . y \<in> x)"

text {* trivial algorithmic tie breaker: take the first element of a list *}
definition tie_breaker_example_alg :: tie_breaker_alg where "tie_breaker_example_alg = hd"

section {* Allocations *}

text {* the value (according to the bids submitted) of a certain allocation *}
definition value_rel :: "bids \<Rightarrow> allocation_rel \<Rightarrow> price"
where "value_rel b buyer  = (\<Sum> y \<in> Domain buyer . b (buyer ,, y) y
  (* CL@CR: This implicitly assumes a value of 0 for goods not sold.  OK?
            Goods not sold don't occur in the potential_buyer relation and 
            therefore won't be summands of this sum. *)
)"

(* CL: probably not needed, neither for close-to-paper nor for computable version
definition value_fun :: "bids \<Rightarrow> allocation_fun \<Rightarrow> price"
where "value_fun b Yp  = (let Y = fst Yp; buyer = snd Yp in
  \<Sum> y \<in> Y . (let n = buyer y in 
    case n of None \<Rightarrow> 0 (* CL@CR: OK to assume a value of 0 for goods not sold? *)
            | Some n \<Rightarrow> b n y))"
*)

text {* all possible allocations of a set of goods to a set of participants: 
  injective functions that map sets of goods to their potential buyers, i.e.\ participants *}
definition possible_allocations_rel :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel set"
where "possible_allocations_rel G N = \<Union> { injections Y N | Y . Y \<in> all_partitions G }" 

notepad
begin
  fix Rs::"('a \<times> 'b) set set"
  fix Sss::"'a set set"
  fix P::"'a set \<Rightarrow> ('a \<times> 'b) set set"
  (* TODO CL: an example (to be mentioned in the paper) for how hard set theory is for Isabelle:
     takes several minutes to find, 104 ms to prove *)
  have "{ R . \<exists> Y \<in> Sss . R \<in> P Y } = \<Union> { P Y | Y . Y \<in> Sss }" by (smt Collect_cong Union_eq mem_Collect_eq)
end

text {* algorithmic version of @{const possible_allocations_rel} *}
fun possible_allocations_alg :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel list"
where "possible_allocations_alg G N = concat [ injections_alg Y N . Y \<leftarrow> all_partitions_alg G ]"

(* example (uncomment to run): possibilities to allocate goods {1,2,3} to participants {100,200} *)
(*
value "possible_allocations_alg {1,2,3::nat} {100,200::nat}"
*)

(* CL: probably not needed, neither for close-to-paper nor for computable version
definition possible_allocations_fun :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_fun set"
where "possible_allocations_fun G N = { (Y,potential_buyer) .
  Y \<in> all_partitions G
  \<and> (\<forall> y \<in> Y . (\<exists> n \<in> N . potential_buyer y = Some n) \<or> potential_buyer y = None)
  \<and> inj_on potential_buyer Y
 }"
*)

end

