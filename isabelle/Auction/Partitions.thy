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

(* 
Set: {a}
Partitions: {{a}}

Set: {a,b}
Partitions: {{a}, {b}}, {{a, b}}

Set: {a,b,c}
Partitions: {{a}, {b}, {c}}, {{a,b}, {c}}, {{a,c}, {b}}, {{a}, {c,b}}, {{a,b,c}}

http://en.wikipedia.org/wiki/Bell_number (number of partitions of a set = number of equivalence relations on a set)
*)

fun all_partitions_fun_list :: "'a list \<Rightarrow> 'a set list list"
  where "all_partitions_fun_list [] = []"
      | "all_partitions_fun_list [x] = [[{x}]]" (* singleton case is special, not sufficiently covered by [] and x#xs *)
      | "all_partitions_fun_list (x # xs) = (let xs_partitions = all_partitions_fun_list xs in
        concat [  
          (* inserting x into each equivalence class \<dots> *)
          [ P[(nat i):={x} \<union> (nth P (nat i))] . i \<leftarrow> [0..(int (List.length P) - 1)] ]
        . P \<leftarrow> xs_partitions (* \<dots> of each partition of xs *) ]
        @ [ {x} # P . P \<leftarrow> xs_partitions] (* and adding the {x} singleton equivalence class to each partition of xs: *)
        )"

(* example using the list representation *)
value "all_partitions_fun_list [1::nat,2,3]"

(* need to turn 'a set list list into 'a set set set *)
fun all_partitions_fun :: "'a::linorder set \<Rightarrow> 'a set set set"
  where "all_partitions_fun A = set (map (\<lambda>P . set P) (all_partitions_fun_list (sorted_list_of_set A)))"

(* example using the set representation *)
value "all_partitions_fun {1::nat,2,3,4}"

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

code_include Scala ""
{*package partition
*}
export_code all_partitions_fun in Scala
module_name Partition file "code/partition.scala"

end
