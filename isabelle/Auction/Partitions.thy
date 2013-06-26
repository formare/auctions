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

(* True iff E is the set of all equivalence relations on the set X *)
definition isEquivSet :: "('a \<times> 'a) set set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "isEquivSet E X \<longleftrightarrow> (\<forall> e . e \<in> E \<longleftrightarrow> equiv X e)"

(* partition of a set w.r.t. an equivalence relation: *)
value "{1::nat} // {(1::nat,1::nat)}"

(* This is really an equivalence relation. *)
lemma "equiv {1::nat} {(1::nat,1::nat)}" unfolding equiv_def refl_on_def sym_def trans_def by fast

(* This should work (returning {(1::nat,1::nat)}) but doesn't.
   Seems we really need a recursive function that enumerates
   all equivalence relations over a set (or even directly all partitions of the set). *)
(* This list post seems related: https://groups.google.com/d/msg/fa.isabelle/SwVl-K3bvFs/DKyQDrE917gJ *)
value "{R \<in> {{(1::nat,1::nat)}} . equiv {1::nat} R}"

(* The following definition is well-defined but not computable: *)
definition allPartitions :: "'a set \<Rightarrow> 'a set set set"
  where "allPartitions A = { P . (* all sets P such that \<dots> *)
    P \<in> Pow (Pow A) (* P is a set of subsets of A,
                       i.e. a subset of the set of all subsets of A,
                       i.e. a subset of the powerset of A,
                       i.e. a member of the powerset of the powerset of A.
                       We need this only for computability; otherwise 'P = A // e' would do the job. *)
    \<and> (\<exists> R . (* There is an R such that \<dots> *)
      equiv A R (* R is an equivalence relation on A *)
      \<and> P = A // R (* and P is the partition of A w.r.t. R. *)
    ) }" (* CL@MC: I think we need to be able to enumerate
            the set of all equivalence relations over a given set
            in a computable way. *)



(* TODO CL: implement computable function
fun partition :: "'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a set" where
  "partition [] [] = {}" |
  "partition (x # xs) b = {}" |
  "partition a (x # xs) = {}"
*)

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
