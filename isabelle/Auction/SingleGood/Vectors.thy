(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>
* Makarius Wenzel <wenzel@lri.fr>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)


header {* Vectors, implemented as functions from an index set to some other set *}

theory Vectors
imports Main
begin

subsection {* Preliminaries *}

type_synonym index = "nat"
type_synonym 'a vector = "index \<Rightarrow> 'a"

subsubsection {* Some component-wise operations for vectors *}

definition zero :: "'a::zero vector"
  where "zero = (\<lambda> x. 0)"

definition le :: "index set \<Rightarrow> ('a::ord) vector \<Rightarrow> ('a::ord) vector \<Rightarrow> bool"
  where "le N v w \<longleftrightarrow> (\<forall>i \<in> N . v i \<le> w i)"

definition eq :: "index set \<Rightarrow> 'a vector \<Rightarrow> 'a vector \<Rightarrow> bool"
  where "eq N v w \<longleftrightarrow> (\<forall>i \<in> N . v i = w i)"

definition non_negative :: "index set \<Rightarrow> 'a::{zero,ord} vector \<Rightarrow> bool"
  where "non_negative N v \<longleftrightarrow> le N zero v"

definition positive :: "index set \<Rightarrow> 'a::{zero,ord} vector \<Rightarrow> bool"
  where "positive N v \<longleftrightarrow> le N zero v \<and> \<not>eq N zero v"

end
