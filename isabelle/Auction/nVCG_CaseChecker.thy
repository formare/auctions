(*
$Id$

Auction Theory Toolbox

Authors:
* Manfred Kerber <m.kerber@cs.bham.ac.uk>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Makarius Wenzel <wenzel@lri.fr>
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Vickrey's Theorem: second price auctions are
  efficient, and truthful bidding is a weakly dominant strategy --
  copy to experiment with ``case checking'' *}

theory nVCG_CaseChecker
imports Complex_Main
  (* "~~/src/HOL/Library/Function_Algebras" (* was needed when we added vectors component-wise *) *)
  "~~/src/HOL/Library/Order_Relation"
  "~~/src/HOL/Library/Efficient_Nat"
  Vectors
  Partitions
  RelationProperties
  Maximum
begin

(*
We can assume or not assume (as it suits us) free disposal, i.e. bid A \<union> B \<ge> max (bid A) (bid B).

For now assume that the value of the goods to the seller is 0.
We are free to assume or not to assume (as it suits us) \<Sum> n \<in> N . x n \<le> x 0, or \<Sum> n \<in> N . x n = x 0.
*)

section {* Combinatorial auctions *}

subsection {* Preliminaries *}

type_synonym participant = index
type_synonym goods = "nat set" (* actually we'd prefer "'a set", as we really don't care about the type *)
type_synonym price = nat (* or maybe "real", later *)

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
type_synonym allocation_fun = "(goods set) \<times> (goods \<rightharpoonup> participant)"
type_synonym allocation_rel = "(goods set) \<times> ((goods \<times> participant) set)"
type_synonym tie_breaker_rel = "(allocation_rel set) \<Rightarrow> allocation_rel"
type_synonym tie_breaker_fun = "(allocation_fun set) \<Rightarrow> allocation_fun"

(* a particular example for bids: *)
definition bb :: bids
where "bb x y = x"

(* a particular example for the "potential buyer" relation: *)
definition ff :: "(goods \<times> participant) set"
where "ff = {(g,p) . p = 1}"

(* the revenue gained from selling a certain allocation (assuming relational allocations) *)
definition revenue_rel :: "bids \<Rightarrow> allocation_rel \<Rightarrow> price"
where "revenue_rel b Yp  = (let Y = fst Yp; potential_buyer = snd Yp in
  \<Sum> y \<in> Y . (let buyer = as_part_fun potential_buyer y in
    case buyer of None \<Rightarrow> 0
                | Some n \<Rightarrow> b n y))"

(* the revenue gained from selling a certain allocation (assuming functional allocations) *)
definition revenue_fun :: "bids \<Rightarrow> allocation_fun \<Rightarrow> price"
where "revenue_fun b Yp  = (let Y = fst Yp; potential_buyer = snd Yp in
  \<Sum> y \<in> Y . (let buyer = potential_buyer y in 
    case buyer of None \<Rightarrow> 0 (* CL@CR: OK to assume a value of 0 for goods not sold? *)
                | Some n \<Rightarrow> b n y))"

(* the set of possible allocations of a set of goods to a set of participants (assuming relational allocations) *)
definition possible_allocations_rel :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel set"
where "possible_allocations_rel G N = { (Y,potential_buyer) .
  Y \<in> allPartitions G
  \<and> Domain potential_buyer \<subseteq> Y
  \<and> Range potential_buyer \<subseteq> N
  \<and> right_unique potential_buyer (* no longer need totality on Y as we are allowing for goods not to be allocated *)
  \<and> injective potential_buyer
 }"

(* the list of possible allocations of a set of goods to a set of participants (computable version) *)
fun possible_allocations_comp :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel list"
where "possible_allocations_comp G N =
  concat [
      [ (set Y, potential_buyer) . potential_buyer \<leftarrow> injective_functions_list Y (sorted_list_of_set N) ]
    . Y \<leftarrow> all_partitions_fun_list (sorted_list_of_set G) ]"

(* example: possibilities to allocate goods {1,2,3} to participants {100,200} *)
value "possible_allocations_comp {1,2,3::nat} {100,200::nat}"

(* the set of possible allocations of a set of goods to a set of participants (assuming functional allocations) *)
definition possible_allocations_fun :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_fun set"
where "possible_allocations_fun G N = { (Y,potential_buyer) .
  Y \<in> allPartitions G
  \<and> (\<forall> y \<in> Y . (\<exists> n \<in> N . potential_buyer y = Some n) \<or> potential_buyer y = None)
  \<and> inj_on potential_buyer Y
 }"

(* the maximum revenue over all possible allocations (assuming relational allocations) *)
definition max_revenue :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> price"
where "max_revenue b G N = Max ((revenue_rel b) ` (possible_allocations_rel G N))"
(* we don't need the variant that assumes functional allocations, as it's really just the same *)

(* TODO CL: this is not yet computational; there is some typing problem maybe in revenue_rel_def *)
fun max_revenue_comp :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> price"
where "max_revenue_comp b G N = maximum_comp_list (possible_allocations_comp G N) (revenue_rel b)"

(* This is the "arg max", where max_revenue is the "max" (assuming relational allocations). *)
definition winning_allocations_rel :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> (allocation_rel set)"
where "winning_allocations_rel b G N = 
{ (Y,potential_buyer) . revenue_rel b (Y,potential_buyer) = max_revenue b G N}"

(* This is the "arg max", where max_revenue is the "max" (assuming functional allocations). *)
definition winning_allocations_fun :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> (allocation_fun set)"
where "winning_allocations_fun b G N = 
{ (Y,potential_buyer) . revenue_fun b (Y,potential_buyer) = max_revenue b G N}"

(* example: break ties by preferring an arbitrary allocation (assuming relational allocations) *)
definition tt_rel :: tie_breaker_rel where "tt_rel x = (THE y . y \<in> x)"

(* example: break ties by preferring an arbitrary allocation (assuming functional allocations) *)
definition tt_fun :: tie_breaker_fun where "tt_fun x = (THE y . y \<in> x)"

(* CL@MC: not sure \<nat> does what we want; and in any case our participants and goods sets are assumed to be finite. *)
definition NN :: "participant set" where "NN = \<nat>"
definition GG :: goods where "GG = \<nat>"

(* the unique winning allocation that remains after tie-breaking (assuming relational allocations) *)
fun winning_allocation_rel :: "tie_breaker_rel \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> allocation_rel"
where "winning_allocation_rel t b G N  = t (winning_allocations_rel b G N)"

(* the unique winning allocation that remains after tie-breaking (assuming functional allocations) *)
definition winning_allocation_fun :: "tie_breaker_fun => bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> allocation_fun"
where "winning_allocation_fun t b G N  = t (winning_allocations_fun b G N)"

(* the value reportedly generated by value maximization problem when solved without n's bids *)
definition \<alpha> :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "\<alpha> b G N n = max_revenue b G (N - {n})"

definition w2g :: "tie_breaker_fun => bids => goods => (participant set) => participant option => goods" 
where "w2g t b G N = inv (snd (winning_allocation_fun t b G N))"

definition foo where "foo t b G N n = b n (w2g t b G N (Some n))" (* won_set *)
definition bar where "bar t b G N = (%n . foo t b G N n)"
definition ss :: "tie_breaker_fun => bids => goods => (participant set) => participant => price"
where "ss t b G N n = setsum (bar t b G N) (N-{n})"

definition payments_fun :: "tie_breaker_fun => bids => goods => (participant set) => (participant => price)"
where "payments_fun t b G N = \<alpha> b G N - ss t b G N"

definition payments_rel :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> tie_breaker_rel \<Rightarrow> participant \<Rightarrow> price"
where "payments_rel b G N t n = 
  (let winning_allocation =
    as_function (inverse (snd (t (winning_allocations_rel b G N))))
   in
     \<alpha> b G N n - 
     (\<Sum> m \<in> N - {n} . b m (winning_allocation m)) )"

(*
declare [[show_types]]
*)

end

