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
  "~~/src/HOL/Library/Function_Algebras"
  "~~/src/HOL/Library/Order_Relation"
  "~~/src/HOL/Library/Efficient_Nat"
  Vectors
  Partitions
  
begin

section {* Combinatorial auctions *}

subsection {* Preliminaries *}

type_synonym participant = index
type_synonym goods = "nat set" (* actually we'd prefer "'a set", as we really don't care about the type *)
type_synonym price = nat (* or maybe real, later *)

(*
(* one participant's bid on a set of goods *)
definition b :: "participant \<Rightarrow> goods \<Rightarrow> nat" where "b i y = (\<Sum> x \<in> y . x)"

(* for one set of goods in one particular partition of the overall set of goods, \<dots> *)
definition f :: "goods \<Rightarrow> participant" where "f Y = (if Y = {} then 1 else 0)"

(* *)
definition h :: "(goods \<Rightarrow> participant) \<Rightarrow> goods \<Rightarrow> nat" where "h F y = b (F y) y"

value "\<lambda> Y f . \<Sum> y \<in> Y . h f y"
*)

(*
value "Max ((\<lambda> Yf::((goods set) \<times> (goods \<Rightarrow> participant)) . let Y = fst Yf; f = snd Yf in \<Sum> y \<in> Y . h f y) ` {(Y, f) . True})"
*)

(* definition h (f, b) = % y . *)

notepad
begin
  def participants \<equiv> "{1::nat, 2}"
  def goods \<equiv> "{3::nat, 4}"
  def bids \<equiv> "\<lambda> (y::nat set) . 51::nat"
  (*
  value "\<Sum> x \<in> {{3::nat},{4}} . h x"
  *)
end

(* equivalence classes and partitions *)

(* CL: maybe uncomment and use as an alternative representation

text{* convenience type synonyms for most of the basic concepts we are dealing with *}
type_synonym endowment = "nat vector" (* conceptually: good \<Rightarrow> quantity *)
type_synonym endowment_subset = "nat vector" (* conceptually the same, but \<le> endowment *)
*)

(* A single participant ascribes real values to subsets of the endowment. *)
(*
type_synonym valuation = "endowment_subset \<Rightarrow> real"

type_synonym valuations = "valuation vector"
*)

(*
type_synonym bid = "endowment_subset \<Rightarrow> real"
(* endowment = (1,2)
   bid = { (0,1) \<rightarrow> 3.45, (1,2) \<rightarrow> 7.42, \<dots> } *)
*)
(*
(* A well-formed bid is non-negative for each “subset” of the endowment, i.e. each vector s
   that is component-wise 0 \<le> s \<le> x0. *)
definition bid :: "bid \<Rightarrow> goods \<Rightarrow> endowment \<Rightarrow> bool"
  where "bid b K x0 \<longleftrightarrow> (\<forall> s . non_negative_real_vector K s \<and> vector_le K s x0 \<longrightarrow> b s \<ge> 0)"

type_synonym allocation = "participant \<Rightarrow> endowment_subset"

(* x0 = (1,2) 
   x1 = (1,1)
   x2 = (0,1) <- K
    ^
    N
*)

value "(\<lambda>z::nat . ((\<lambda>x::nat.2*x) z + (\<lambda>x::nat.1) z)) 3::nat"
value "((\<lambda>x::nat.2*x) + (\<lambda>x::nat.1)) 3::nat"

definition allocation :: "participants \<Rightarrow> goods \<Rightarrow> allocation \<Rightarrow> bool"
  where "allocation N K x \<longleftrightarrow> 
    (\<Sum> i \<in> N . x i)

non_negative_real_vector N x \<and> (\<Sum> i \<in> N . x i) = 1"


type_synonym payments = "real vector"
*)
(* MC: Some tries *)

type_synonym bids = "participant \<Rightarrow> goods \<Rightarrow> price"
type_synonym allocation = "(goods set) \<times> (goods \<Rightarrow> participant)"

definition h :: "bids => (goods \<Rightarrow> participant) => goods => price"
where "h b potential_buyer y = b (potential_buyer y) y"

(* a particular example for bids: *)
definition bb :: "bids"
where "bb x y = x"

(* a particular example for the "potential buyer" function: *)
definition ff :: "goods \<Rightarrow> participant"
where "ff x = 1"

value "% Y potential_buyer . setsum ((h b potential_buyer) :: goods \<Rightarrow> price) Y"

definition F :: "bids => allocation => price"
where "F b Yp  = (let Y = fst Yp; potential_buyer = snd Yp in
  \<Sum> y \<in> Y . b (potential_buyer y) y)"

definition possible_allocations :: "goods => participant set  => allocation set"
where "possible_allocations G N = {(Y,potential_buyer). Y \<in> allPartitions G & (\<forall> x :: goods . x \<in> Y \<longrightarrow> potential_buyer x \<in> N) }"

definition max_revenue :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> price"
where "max_revenue b G N = Max ((F b) ` (possible_allocations G N))"

definition winning_allocations (* "arg max" *) :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> allocation set"
where "winning_allocations b G N = 
{ (Y,potential_buyer) . F b (Y,potential_buyer) = max_revenue b G N}"

type_synonym tie_breaker = "allocation set \<Rightarrow> allocation"

definition alpha :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> participant \<Rightarrow> price"
where "alpha b G N n = max_revenue b G (N - {n})"

definition payments :: "bids \<Rightarrow> goods \<Rightarrow> participant set \<Rightarrow> tie_breaker \<Rightarrow> participant \<Rightarrow> price"
where "payments b G N t n = alpha b G N n - FOO (t (winning_allocations b G N))"

notepad
begin
  def foo \<equiv> "(F bb) ` (possible_allocations {x::nat . True} {x::nat . True})"
end

end
