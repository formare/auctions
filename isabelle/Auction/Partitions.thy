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
imports Main Complete_Lattices
begin

(* don't need the following for now; just thought we might need it for computability:
(* True iff E is the set of all equivalence relations on the set X *)
definition isEquivSet :: "('a \<times> 'a) set set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "isEquivSet E X \<longleftrightarrow> (\<forall> e . e \<in> E \<longleftrightarrow> equiv X e)"
*)

(* partition of a set w.r.t. an equivalence relation: *)
(*
value "{1::nat} // {(1::nat,1::nat)}"
*)

(* an inference rule needed below *)
(*
lemma equalitySubsetI: "(\<And>x . x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x . x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B" by fast
*)

(* testing a concrete partition, this time not with "value" *)
(*
lemma partition_example: "{1::nat} // {(1::nat,1::nat)} = {{1::nat}}" (is "?lhs = ?rhs")
proof (rule equalitySubsetI)
  fix x assume "x \<in> ?lhs"
  then have "x \<in> {{(1::nat, 1)} `` {1::nat}}" by (metis singleton_quotient)
  then show "x \<in> ?rhs" by auto
next
  fix x assume "x \<in> ?rhs"
  then have "x \<in> {{(1::nat, 1)} `` {1::nat}}" by fast
  then show "x \<in> ?lhs" by (metis singleton_quotient)
qed
*)
  
(* This is really an equivalence relation. *)
(*
lemma "equiv {1::nat} {(1::nat,1::nat)}" unfolding equiv_def refl_on_def sym_def trans_def by fast
*)

(* This should work (returning {(1::nat,1::nat)}) but doesn't.
   Seems we really need a recursive function that enumerates
   all equivalence relations over a set (or even directly all partitions of the set). *)
(* This list post seems related: https://groups.google.com/d/msg/fa.isabelle/SwVl-K3bvFs/DKyQDrE917gJ *)
(*
value "{R \<in> {{(1::nat,1::nat)}} . equiv {1::nat} R}"
*)

(* The following definition is well-defined but not computable: *)
definition allPartitions :: "'a set \<Rightarrow> 'a set set set"
  where "allPartitions A = { P . (* all sets P such that \<dots> *)
    (* thought we'd need something like this for computability:
    P \<in> Pow (Pow A) (* P is a set of subsets of A,
                       i.e. a subset of the set of all subsets of A,
                       i.e. a subset of the powerset of A,
                       i.e. a member of the powerset of the powerset of A.
                       We need this only for computability; otherwise 'P = A // e' would do the job. *)
    \<and> *)
    (\<exists> R . (* There is an R such that \<dots> *)
      equiv A R (* R is an equivalence relation on A *)
      \<and> P = A // R (* and P is the partition of A w.r.t. R. *)
    ) }"

(* testing allPartitions *)
(*
lemma "{{1::nat}} \<in> allPartitions {1::nat}" (is "?P \<in> allPartitions ?A")
proof -
  def R \<equiv> "{(1::nat,1::nat)}"
  then have "equiv ?A R" unfolding equiv_def refl_on_def sym_def trans_def by fast
  moreover have "?A // R = ?P" unfolding R_def using partition_example .
  ultimately show "?thesis" unfolding allPartitions_def by auto
qed
*)

(* TODO CL: implement computable function
fun partition :: "'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a set" where
  "partition [] [] = {}" |
  "partition (x # xs) b = {}" |
  "partition a (x # xs) = {}"
*)

end
