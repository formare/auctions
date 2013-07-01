(*
$Id$

Auction Theory Toolbox

Authors:
* Manfred Kerber <m.kerber@cs.bham.ac.uk>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
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
type_synonym allocation_rel = "((goods \<times> participant) set)" (* goods set not necessary as a function-as-relation-as-set representation carries its own domain :-) *)
type_synonym tie_breaker_rel = "allocation_rel set \<Rightarrow> allocation_rel"
type_synonym tie_breaker_fun = "allocation_fun set \<Rightarrow> allocation_fun"
type_synonym tie_breaker_comp = "allocation_rel list \<Rightarrow> allocation_rel"

(* a particular example for bids: *)
definition b_example :: bids
where "b_example x y = x"

(* example: break ties by preferring an arbitrary allocation (we omit type annotations so that we can use this with 
   both relational and functional allocation) *)
definition tie_breaker_example :: tie_breaker_rel where "tie_breaker_example x = (THE y . y \<in> x)"
(* trivial tie-breaking for allocation lists: take the first one with "hd list" *)
definition tie_breaker_example_comp :: tie_breaker_comp where "tie_breaker_example_comp = hd"

definition paper_example_participants :: "participant set" where "paper_example_participants = {1::nat, 2, 3}"
definition paper_example_goods :: goods where "paper_example_goods = {(* A *) 11, (* B *) 12}"
definition paper_example_bids :: bids where "paper_example_bids bidder goods = (
      if (bidder = 1 \<and> goods = {11,12}
          \<or> (bidder = 2 \<or> bidder = 3) \<and> card goods = 1)
      then 2
      else 0)"

(* the revenue gained from selling a certain allocation (assuming relational allocations) *)
definition revenue_rel :: "bids \<Rightarrow> allocation_rel \<Rightarrow> price"
where "revenue_rel b buyer  = (\<Sum> y \<in> Domain buyer . b (eval_rel_or buyer y 0) y
  (* CL@CR: This implicitly assumes a value of 0 for goods not sold.  OK?
            Goods not sold don't occur in the potential_buyer relation *)
)"

(* the revenue gained from selling a certain allocation (assuming functional allocations) *)
definition revenue_fun :: "bids \<Rightarrow> allocation_fun \<Rightarrow> price"
where "revenue_fun b Yp  = (let Y = fst Yp; buyer = snd Yp in
  \<Sum> y \<in> Y . (let n = buyer y in 
    case n of None \<Rightarrow> 0 (* CL@CR: OK to assume a value of 0 for goods not sold? *)
            | Some n \<Rightarrow> b n y))"

(* the set of possible allocations of a set of goods to a set of participants (assuming relational allocations) *)
definition possible_allocations_rel :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel set"
where "possible_allocations_rel G N = { potential_buyer . \<exists> Y \<in> allPartitions G . 
  Domain potential_buyer \<subseteq> Y
  \<and> Range potential_buyer \<subseteq> N
  \<and> right_unique potential_buyer (* no longer need totality on Y as we are allowing for goods not to be allocated *)
  \<and> injective potential_buyer
 }"

(* the list of possible allocations of a set of goods to a set of participants (computable version) *)
fun possible_allocations_comp :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_rel list"
where "possible_allocations_comp G N =
  concat [
      [ potential_buyer . potential_buyer \<leftarrow> injective_functions_list Y (sorted_list_of_set N) ]
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

fun max_revenue_comp :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> price"
where "max_revenue_comp b G N = maximum_comp_list (possible_allocations_comp G N) (revenue_rel b)"

value "max_revenue_comp paper_example_bids paper_example_goods paper_example_participants"

(* This is the "arg max", where max_revenue is the "max" (assuming relational allocations). *)
definition winning_allocations_rel :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> allocation_rel set"
where "winning_allocations_rel b G N = 
{ potential_buyer . revenue_rel b potential_buyer = max_revenue b G N}"

(* This is the "arg max", where max_revenue is the "max" (assuming functional allocations). *)
definition winning_allocations_fun :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> allocation_fun set"
where "winning_allocations_fun b G N = 
{ (Y,potential_buyer) . revenue_fun b (Y,potential_buyer) = max_revenue b G N}"

(* the unique winning allocation that remains after tie-breaking (assuming relational allocations) *)
fun winning_allocation_rel :: "tie_breaker_rel \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> allocation_rel"
where "winning_allocation_rel t b G N  = t (winning_allocations_rel b G N)"

(* the unique winning allocation that remains after tie-breaking (assuming functional allocations) *)
definition winning_allocation_fun :: "tie_breaker_fun \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> allocation_fun"
where "winning_allocation_fun t b G N  = t (winning_allocations_fun b G N)"

definition winning_allocations_comp_CL
where "winning_allocations_comp_CL b G N = (arg_max_comp_list
    (possible_allocations_comp G N)
    (revenue_rel b))"

value "winning_allocations_comp_CL
  paper_example_bids
  paper_example_goods
  paper_example_participants"

definition winning_allocations_comp_MC where 
"winning_allocations_comp_MC b G N = (let all = possible_allocations_comp G N in
  map (nth all) (max_positions (map (revenue_rel b) all)))"

value "winning_allocations_comp_MC 
  paper_example_bids
  paper_example_goods
  paper_example_participants"

(* the value reportedly generated by value maximization problem when solved without n's bids *)
definition \<alpha> :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "\<alpha> b G N n = max_revenue b G (N - {n})"

definition \<alpha>_comp :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "\<alpha>_comp b G N n = max_revenue_comp b G (N - {n})"

definition winners'_goods_fun :: "tie_breaker_fun \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant option \<Rightarrow> goods" 
where "winners'_goods_fun t b G N = inv (snd (winning_allocation_fun t b G N))"

definition remaining_value_fun :: "tie_breaker_fun \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "remaining_value_fun t b G N n =
  (\<Sum> m \<in> N - {n} . b m (winners'_goods_fun t b G N (Some m)))"

definition remaining_value_rel :: "tie_breaker_rel \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "remaining_value_rel t b G N n =
  (\<Sum> m \<in> N - {n} . b m ((as_function (inverse (t (winning_allocations_rel b G N)))) m))"

definition remaining_value_comp :: "tie_breaker_comp \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "remaining_value_comp t b G N n =
  (\<Sum> m \<in> N - {n} . b m (eval_rel_or (inverse (t (winning_allocations_comp_CL b G N))) m {}))"

definition payments_fun :: "tie_breaker_fun \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "payments_fun t b G N = \<alpha> b G N - remaining_value_fun t b G N"

definition payments_rel :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> tie_breaker_rel \<Rightarrow> participant \<Rightarrow> price"
where "payments_rel b G N t = \<alpha> b G N - remaining_value_rel t b G N"

definition payments_comp :: "tie_breaker_comp \<Rightarrow> bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "payments_comp t b G N = \<alpha>_comp b G N - remaining_value_comp t b G N"

value "{(x, payments_comp hd paper_example_bids paper_example_goods paper_example_participants x) | x . x \<in> paper_example_participants}"

(* example for the single-good auction *)
definition sga_goods :: goods where "sga_goods = {1::nat}"
definition sga_bids :: "(participant \<Rightarrow> price) \<Rightarrow> bids"
where "sga_bids b = (\<lambda> bidder goods . (
      if goods = sga_goods then b bidder else 0))"

value "hd (winning_allocations_comp_CL
  (sga_bids (nth [23::nat, 42, 31]))
  sga_goods
  {0::nat, 1, 2})"
value "{(x, payments_comp hd (sga_bids (nth [23::nat, 42, 31])) sga_goods {0::nat, 1, 2} x) | x . x \<in> {0::nat, 1, 2}}"

(*
declare [[show_types]]
*)

code_include Scala ""
{*package win 
*}
export_code winning_allocations_comp_MC in Scala
(* In SML, OCaml and Scala "file" is a file name; in Haskell it's a directory name ending with / *)
module_name Vickrey file "code/win.scala"


end

