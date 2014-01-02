(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati <marco.caminati@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Additional material that we would have expected in Relation.thy *}

theory RelationUtils
imports
  Main
  SetUtils

begin

section {* Range *}

(* TODO CL: document *)
lemma Range_except:
  fixes R::"('a \<times> 'b) set"
    and N::"'b set"
    and n::'b
  assumes Range: "Range R \<subseteq> N"
  shows "Range { (x, y) . (x, y) \<in> R \<and> y \<noteq> n } = (N - {n}) \<inter> Range R"
proof (rule equalitySubsetI)
  fix y
  assume y: "y \<in> Range { (x, y) . (x, y) \<in> R \<and> y \<noteq> n }"
  have y_in_Range: "y \<in> Range R"
    using y by (metis (lifting, no_types) Range.simps mem_Collect_eq split_conv)
  moreover have "y \<in> N" using y_in_Range by (metis Range in_mono)
  moreover have "y \<noteq> n" using y by (smt Range_Collect_split mem_Collect_eq)
  ultimately show "y \<in> (N - {n}) \<inter> Range R" by blast
next
  fix y
  assume y: "y \<in> (N - {n}) \<inter> Range R"
  have "y \<in> N" using y by fast
  moreover have "y \<noteq> n" using y by fastforce
  moreover have "y \<in> Range R" using y by fast
  ultimately show "y \<in> Range { (x, y) . (x, y) \<in> R \<and> y \<noteq> n }"
    by (metis (lifting, mono_tags) Range.simps mem_Collect_eq prod_caseI)
qed

text{* If @{term z} is not in the range of a binary relation, removing all tuples with @{term z}
  as their second component from the relation doesn't change the relation
  (because no such tuples exist). *}
lemma Range_except_irrelevant:
  assumes "z \<notin> Range R"
  shows "{ (x, y) . (x, y) \<in> R \<and> y \<noteq> z } = R"
(* The following proof found by Sledgehammer in Isabelle2013-1-RC3 takes long, don't remember,
   maybe 63 ms? *)
(* by (smt Collect_mem_eq Range_iff assms cond_split_eta) *)
proof -
  {
    fix x y
    from assms have "(x, y) \<in> R \<longrightarrow> y \<noteq> z" by fast
    then have "(x, y) \<in> R \<and> y \<noteq> z \<longleftrightarrow> (x, y) \<in> R" by fast
  }
  then show ?thesis by auto
qed

section {* Domain *}

text{* If a relation is left-total on a set @{term A}, its superrelations are left-total on @{term A} too. *}
lemma suprel_left_total_on:
  fixes R :: "('a \<times> 'b) set"
    and S :: "('a \<times> 'b) set"
    and A :: "'a set"
  assumes "A \<subseteq> Domain R"
      and "R \<subseteq> Q"
  shows "A \<subseteq> Domain Q"
using assms by fast

(* TODO CL: document *)
lemma Domain_except:
  fixes R::"('a \<times> 'b) set"
    and N::"'a set"
    and n::'a
  assumes Domain: "Domain R \<subseteq> N"
  shows "Domain { (x, y) . (x, y) \<in> R \<and> x \<noteq> n } = (N - {n}) \<inter> Domain R"
(* TODO CL: Sledgehammer in Isabelle2013-1-RC3 can't prove this. *)
proof -
  from Domain have Range: "Range (R\<inverse>) \<subseteq> N" by simp
  have "Domain {(x, y). (x, y) \<in> R \<and> x \<noteq> n} = Range {(y, x). (y, x) \<in> R\<inverse> \<and> x \<noteq> n}"
    using Domain_unfold by auto
  also have "\<dots> = (N - {n}) \<inter> Range (R\<inverse>)" using Range by (rule Range_except)
  also have "\<dots> = (N - {n}) \<inter> Domain R" by simp
  finally show ?thesis .
qed

section {* Image *}

text {* The image of a relation is only effective within the domain of that relation *}
lemma Image_within_domain: "R `` X = R `` (X \<inter> Domain R)"
by fast

text {* An alternative phrasing of @{thm Image_within_domain} *}
lemma Image_within_domain': fixes x R shows "x \<in> Domain R \<longleftrightarrow> R `` {x} \<noteq> {}"
using Image_within_domain by blast

text {* The image of a set outside a relation's domain under that domain is empty. *}
lemma Image_outside_domain:
  fixes X::"'a set"
    and R::"('a \<times> 'b) set"
shows "X \<inter> Domain R = {} \<longleftrightarrow> R `` X = {}"
using Image_within_domain by blast

text {* If the images of two sets @{term X} and @{term Y} under a relation @{term R} are 
  disjoint, @{term X} and @{term Y} are disjoint on the domain of @{term R}. *}
lemma disj_Image_imp_disj_Domain:
  assumes "R `` X \<inter> R `` Y = {}" 
  shows "Domain R \<inter> X \<inter> Y = {}"
using assms by auto

section {* Converse *}

text {* alternative characterisation of the intersection of a relation's domain with some set, in
  terms of the converse relation *}
lemma Domain_Int_wrt_converse: "Domain R \<inter> X \<subseteq> R\<inverse> `` (R `` X)"
by fast

end
