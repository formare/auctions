(*
$Id: Partitions.thy 1274 2013-06-27 10:01:36Z langec $

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

theory RelationProperties
imports Main
begin

definition left_total_on :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool"
where "left_total_on R A \<longleftrightarrow> (\<forall> x \<in> A . \<exists> y . (x, y) \<in> R)"

definition right_unique :: "('a \<times> 'b) set \<Rightarrow> bool"
where "right_unique R \<longleftrightarrow> (\<forall> a \<in> Domain R . card (R `` {a}) \<le> 1)"

definition function_on :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool"
where "function_on R A \<longleftrightarrow> left_total_on R A \<and> right_unique R"

definition as_function :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b"
where "as_function R a = (THE b . b \<in> R `` {a})"

lemma "function_on {(1::nat, 2::nat), (2::nat, 4::nat)} {1::nat}"
unfolding function_on_def left_total_on_def right_unique_def
oops

lemma "(as_function {(1::nat, 2::nat), (2::nat, 4::nat)} 1::nat) = (2::nat)"
unfolding as_function_def
oops

definition injective :: "('a \<times> 'b) set \<Rightarrow> bool"
where "injective R \<longleftrightarrow> (\<forall> a \<in> Domain R . \<forall> b \<in> Domain R . R `` {a} = R `` {b} \<longrightarrow> a = b)"

definition inverse :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'a) set"
where "inverse R = { (y, x) . (x, y) \<in> R }"

end
