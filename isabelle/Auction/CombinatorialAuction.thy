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
begin

section {* Combinatorial auctions *}

subsection {* Preliminaries *}

type_synonym participant = index
type_synonym goods = "nat set" (* actually we'd prefer "'a set", as we really don't care about the type *)
type_synonym price = real

(*
Keeping old initial vector-based bid implementation for reference.
		
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
type_synonym allocation_rel = "((goods \<times> participant) set)" (* goods set not necessary as a function-as-relation-as-set representation carries its own domain :-) *)
type_synonym tie_breaker_rel = "allocation_rel set \<Rightarrow> allocation_rel"
type_synonym tie_breaker_comp = "allocation_rel list \<Rightarrow> allocation_rel"
type_synonym payments = "participant \<Rightarrow> price"

(* CL: probably not needed, neither for close-to-paper nor for computable version
type_synonym allocation_fun = "(goods set) \<times> (goods \<rightharpoonup> participant)"
type_synonym tie_breaker_fun = "allocation_fun set \<Rightarrow> allocation_fun"
*)

type_synonym combinatorial_auction = "((goods \<times> participant set \<times> bids) \<times> (allocation_rel \<times> payments)) set"

(* example: break ties by preferring an arbitrary allocation (we omit type annotations so that we can use this with 
   both relational and functional allocation) *)
definition tie_breaker_example :: tie_breaker_rel where "tie_breaker_example x = (THE y . y \<in> x)"
(* trivial tie-breaking for allocation lists: take the first one with "hd list" *)
definition tie_breaker_example_comp :: tie_breaker_comp where "tie_breaker_example_comp = hd"

(* the example from "The Lovely but Lonely Vickrey Auction" *)
definition paper_example_participants :: "participant set" where "paper_example_participants = {1::nat, 2, 3}"
definition paper_example_goods :: goods where "paper_example_goods = {(* A *) 11, (* B *) 12}"
definition paper_example_bids :: bids where "paper_example_bids bidder goods = (
      if (bidder = 1 \<and> goods = {11,12}
          \<or> (bidder = 2 \<or> bidder = 3) \<and> card goods = 1)
      then 2
      else 0)"
(* the same in CATS format *)
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

(* the revenue gained from selling a certain allocation (assuming relational allocations) *)
definition revenue_rel :: "bids \<Rightarrow> allocation_rel \<Rightarrow> price"
where "revenue_rel b buyer  = (\<Sum> y \<in> Domain buyer . b (buyer ,, y) y
  (* CL@CR: This implicitly assumes a value of 0 for goods not sold.  OK?
            Goods not sold don't occur in the potential_buyer relation and 
            therefore won't be summands of this sum. *)
)"

(* CL: probably not needed, neither for close-to-paper nor for computable version
(* the revenue gained from selling a certain allocation (assuming functional allocations) *)
definition revenue_fun :: "bids \<Rightarrow> allocation_fun \<Rightarrow> price"
where "revenue_fun b Yp  = (let Y = fst Yp; buyer = snd Yp in
  \<Sum> y \<in> Y . (let n = buyer y in 
    case n of None \<Rightarrow> 0 (* CL@CR: OK to assume a value of 0 for goods not sold? *)
            | Some n \<Rightarrow> b n y))"
*)

(* the set of possible allocations of a set of goods to a set of participants (assuming relational allocations) *)
definition possible_allocations_rel :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel set"
where "possible_allocations_rel G N = { potential_buyer . \<exists> Y \<in> all_partitions G . 
  Domain potential_buyer \<subseteq> Y
  \<and> Range potential_buyer \<subseteq> N
  \<and> runiq potential_buyer (* no longer need totality on Y as we are allowing for goods not to be allocated *)
  \<and> injective potential_buyer
 }"

(* the list of possible allocations of a set of goods to a set of participants (computable version) *)
fun possible_allocations_comp :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel list"
where "possible_allocations_comp G N =
  concat [
    injections Y N (* the potential buyers *)
    . Y \<leftarrow> all_partitions_alg G ]"

(* example (uncomment to run): possibilities to allocate goods {1,2,3} to participants {100,200} *)
(*
value "possible_allocations_comp {1,2,3::nat} {100,200::nat}"
*)

(* CL: probably not needed, neither for close-to-paper nor for computable version
(* the set of possible allocations of a set of goods to a set of participants (assuming functional allocations) *)
definition possible_allocations_fun :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_fun set"
where "possible_allocations_fun G N = { (Y,potential_buyer) .
  Y \<in> all_partitions G
  \<and> (\<forall> y \<in> Y . (\<exists> n \<in> N . potential_buyer y = Some n) \<or> potential_buyer y = None)
  \<and> inj_on potential_buyer Y
 }"
*)

(* TODO CL: revise the following as per https://github.com/formare/auctions/issues/19 *)
definition admissible_input where "admissible_input G N b = True"

end

