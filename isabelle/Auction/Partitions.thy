(*
$Id$

Auction Theory Toolbox

Authors:
* Christoph Lange <math.semantic.web@gmail.com>
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory Partitions
imports Main
begin

value "{1::nat} // {(1::nat,1::nat)}"

(* True iff E is the set of all equivalence relations on the set X *)
definition isEquivSet :: "('a \<times> 'a) set set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "isEquivSet E X \<longleftrightarrow> (\<forall> e . e \<in> E \<longleftrightarrow> equiv X e)"

(* TODO CL: implement computable function
fun partition :: "'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a set" where
  "partition [] [] = {}" |
  "partition (x # xs) b = {}" |
  "partition a (x # xs) = {}"
*)

definition partition :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set"
  where "partition G e = { s . s \<subseteq> }"

definition b :: "nat \<Rightarrow> (nat set) \<Rightarrow> nat" where "b i y = (\<Sum> x \<in> y . x)"

definition f :: "nat set \<Rightarrow> nat" where "f Y = (if Y = {} then 1 else 0)"

definition h :: "(nat set \<Rightarrow> nat) \<Rightarrow> (nat set) \<Rightarrow> nat" where "h F y = b (F y) y"

value "\<Sum> y \<in> {{3},{4}} . h f y"

(* definition h (f, b) = % y . *)

notepad
begin
  def participants \<equiv> "{1::nat, 2}"
  def goods \<equiv> "{3::nat, 4}"
  def bids \<equiv> "\<lambda> (y::nat set) . 51::nat"
  value "\<Sum> x \<in> {{3::nat},{4}} . h x"
end

end
