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

begin

section {* Combinatorial auctions *}

subsection {* Preliminaries *}

type_synonym participant = nat
type_synonym participants = "nat set"

type_synonym goods = "nat set" (* actually we'd prefer "'a set", as we really don't care about the type *)

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

(* Bids are of the same type as valuations, but conceptually different. *)
type_synonym bid = ""

(*
type_synonym bid = "endowment_subset \<Rightarrow> real"
(* endowment = (1,2)
   bid = { (0,1) \<rightarrow> 3.45, (1,2) \<rightarrow> 7.42, \<dots> } *)
*)

type_synonym bids = "bid vector"

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



end

