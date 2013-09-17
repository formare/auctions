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
  Relation

begin

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

(* TODO CL: remove for Isabelle2014; has been included in library (http://isabelle.in.tum.de/repos/isabelle/rev/c5096c22892b) *)
text {* The converse of the empty relation is empty. *}
lemma converse_empty: "{}\<inverse> = {}" by fast

(* TODO CL: remove for Isabelle2014; has been included in library (http://isabelle.in.tum.de/repos/isabelle/rev/c5096c22892b) *)
text {* The definition of @{const converse} isn't suitable for generating code, so we provide
  a code equation using an alternative definition. *}
lemma [code_unfold]: "R\<inverse> = { (y, x) . (x, y) \<in> R }" by (rule converse_unfold)

(* TODO CL: probably remove for Isabelle2014, which will have a similar simp rule converse_mono *)
text {* If two relations are subrelations of each other, so are their converse relations. *}
lemma converse_subrel: assumes "P \<subseteq> Q" shows "P\<inverse> \<subseteq> Q\<inverse>"
using assms by fast

text {* alternative characterisation of the intersection of a relation's domain with some set, in
  terms of the converse relation *}
lemma Domain_Int_wrt_converse: "Domain R \<inter> X \<subseteq> R\<inverse> `` (R `` X)"
by fast

end
