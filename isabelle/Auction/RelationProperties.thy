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

theory RelationProperties
imports
  Main
  HOLUtils
  SetUtils
  ListUtils
begin

section {* restriction *}

text {* restriction of a relation to a set (usually resulting in a relation with a smaller domain) *}
definition restrict
(* TODO MC: compare with restr in SchorrWaite.thy
   CL@MC: doesn't seem helpful, as its type "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a) set" is 
   more specific than what we need. *)
:: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "||" 75)
where "R || X = X \<times> (Range R) \<inter> R"

text {* Restricting a relation to the empty set yields the empty set. *}
lemma restrict_empty: "P || {} = {}"
unfolding restrict_def by simp

text {* A restriction is a subrelation of the original relation. *}
lemma restriction_is_subrel: "P || X \<subseteq> P"
using restrict_def by blast

text {* Restricting a relation only has an effect within its domain. *}
lemma restriction_within_domain: "P || X = P || (X \<inter> (Domain P))"
unfolding restrict_def by fast

text {* alternative characterisation of the restriction of a relation to a singleton set *}
lemma restrict_to_singleton: "P || {x} = {x} \<times> P `` {x}"
unfolding restrict_def by fast

section {* relation outside some set *}

text {* For a set-theoretical relation @{term R} and an ``exclusion'' set @{term X}, return those
  tuples of @{term R} whose first component is not in @{term X}.  In other words, exclude @{term X}
  from the domain of @{term R}. *}
definition Outside :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "outside" 75) (* MC: 75 or whatever, for what I know *)
where "Outside R X = R - (X \<times> Range R)"

text {* Considering a relation outside some set @{term X} reduces its domain by @{term X}. *}
lemma outside_reduces_domain: "Domain (P outside X) = Domain P - X"
unfolding Outside_def by fast

text {* For any set, a relation equals the union of its restriction to that set and its
  pairs outside that set. *}
lemma outside_union_restrict: "P = P outside X \<union> P || X"
unfolding Outside_def restrict_def by fast

text {* The range of a relation @{term R} outside some exclusion set @{term X} is a 
  subset of the image of the domain of @{term R}, minus @{term X}, under @{term R}. *}
lemma Range_outside_sub_Image_Domain: "Range (R outside X) \<subseteq> R `` (Domain R - X)"
using Outside_def Image_def Domain_def Range_def by blast

section {* evaluation as a function *}

text {* Evaluates a relation @{term R} for a single argument, as if it were a function.
  This will only work if @{term R} is a total function, i.e. if the image is always a singleton set. *}
fun eval_rel :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" (infix ",," 75) (* . (Mizar's notation) confuses Isar *)
where "eval_rel R a = the_elem (R `` {a})"

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

section {* right-uniqueness *}

text {* right-uniqueness of a relation: the image of a @{const trivial} set (i.e.\ an empty or
  singleton set) under the relation is trivial again. *}
definition runiq :: "('a \<times> 'b) set \<Rightarrow> bool" where
"runiq R = (\<forall> X . trivial X \<longrightarrow> trivial (R `` X))"

text {* alternative characterisation of right-uniqueness: the image of a singleton set is
   @{const trivial}, i.e.\ an empty or singleton set. *}
lemma runiq_alt: "runiq R \<longleftrightarrow> (\<forall> x . trivial (R `` {x}))"
(* CL: The following proof, found by Sledgehammer, takes 26 ms on my machine. *)
(* unfolding runiq_def by (metis Image_empty trivial_cases trivial_empty trivial_singleton) *)
proof
  assume runiq: "runiq R"
  show "\<forall> x . trivial (R `` {x})"
  proof
    fix x::'a
    have "trivial {x}" unfolding trivial_def by simp
    with runiq show "trivial (R `` {x})" unfolding runiq_def by fast
  qed
next
  assume triv: "\<forall> x . trivial (R `` {x})"
  have "\<forall> X::'a set . trivial X \<longrightarrow> trivial (R `` X)"
  proof (rule allImpI)
    fix X::"'a set"
    assume trivial: "trivial X"
    then show "trivial (R `` X)"
    proof (cases rule: trivial_cases)
      case empty
      then show ?thesis unfolding trivial_def by simp
    next
      case (singleton x)
      with singleton triv show ?thesis by fast
    qed
  qed
  then show "runiq R" unfolding runiq_def by fast
qed

text {* an alternative definition of right-uniqueness in terms of @{const eval_rel} *}
lemma runiq_wrt_eval_rel:
  fixes R :: "('a \<times> 'b) set"
  shows "runiq R = (\<forall>x . R `` {x} \<subseteq> {R ,, x})"
by (metis eval_rel.simps runiq_alt trivial_def)

text {* A subrelation of a right-unique relation is right-unique. *}
lemma subrel_runiq:
  fixes Q::"('a \<times> 'b) set"
    and R::"('a \<times> 'b) set"
  assumes runiq_sup: "runiq Q"
      and subset: "R \<subseteq> Q"
shows "runiq R"
unfolding runiq_def
proof (rule allImpI)
  fix X::"'a set"
  assume "trivial X"
  then have "trivial (Q `` X)" using runiq_sup unfolding runiq_def by fast
  then show "trivial (R `` X)" using subset by (metis (full_types) Image_mono equalityE trivial_subset)
qed

text {* If two right-unique relations have disjoint domains, their union is right-unique too. *}
lemma disj_Un_runiq:
  fixes P::"('a \<times> 'b) set"
    and Q::"('a \<times> 'b) set"
  assumes runiq_P: "runiq P"
      and runiq_Q: "runiq Q"
      and disj_Dom: "Domain P \<inter> Domain Q = {}"
  shows "runiq (P \<union> Q)"
proof -
  have "\<forall> x . trivial ((P \<union> Q) `` {x})"
  proof
    fix x
    have triv_Im_P: "trivial (P `` {x})" using runiq_P runiq_alt by fast
    have triv_Im_Q: "trivial (Q `` {x})" using runiq_Q runiq_alt by fast
    have "(P \<union> Q) `` {x} = P `` {x} \<union> Q `` {x}" by fast
    with disj_Dom have "(P \<union> Q) `` {x} = P `` {x} \<or> (P \<union> Q) `` {x} = Q `` {x}" by blast
    then show "trivial ((P \<union> Q) `` {x})" using triv_Im_P triv_Im_Q by force
  qed
  then show ?thesis using runiq_alt by fast
qed

text {* A singleton relation is right-unique. *}
lemma runiq_singleton_rel: "runiq {(x, y)}" (is "runiq ?R")
unfolding runiq_def
proof (rule allImpI)
  fix X::"'a set"
  assume "trivial X"
  then show "trivial (?R `` X)"
  proof (cases rule: trivial_cases)
    case empty
    then show ?thesis unfolding trivial_def by simp
  next
    case (singleton z)
    show ?thesis
    proof (cases "x = z")
      case True
      then have "?R `` {z} = {y}" by fast
      with singleton show ?thesis by (simp add: trivial_singleton)
    next
      case False
      then have "?R `` {z} = {}" by blast
      with singleton show ?thesis by (simp add: trivial_empty)
    qed
  qed
qed

text {* A trivial relation is right-unique *}
lemma runiq_trivial_rel:
  assumes "trivial R"
  shows "runiq R"
using assms runiq_singleton_rel by (metis subrel_runiq surj_pair trivial_def)

text {* alternative characterisation of the fact that, if a relation @{term R} is right-unique,
  its evaluation @{term "R,,x"} on some argument @{term x} in its domain, occurs in @{term R}'s
  range. *}
lemma eval_runiq_rel:
  assumes domain: "x \<in> Domain R"
      and runiq: "runiq R" 
  shows "(x, R,,x) \<in> R"
proof -
  have "trivial (R `` {x})" using runiq unfolding runiq_alt by fast
  then show ?thesis
  proof (cases rule: trivial_cases)
    case empty
    with domain have False by fast
    then show ?thesis ..
  next
    case (singleton y)
    then have "R ,, x = y" by simp
    with singleton show ?thesis by blast
  qed
qed

text {* The image of a singleton set under a right-unique relation is a singleton set. *}
lemma Image_runiq_eq_eval:
  assumes "x \<in> Domain R"
      and "runiq R" 
  shows "R `` {x} = {R ,, x}"
using assms runiq_wrt_eval_rel
by (metis Image_within_domain' subset_singletonD)

text {* If the images of two sets @{term X} and @{term Y} under a relation @{term R} are 
  disjoint, @{term X} and @{term Y} are disjoint on the domain of @{term R}. *}
lemma disj_Image_imp_disj_Domain:
  assumes "R `` X \<inter> R `` Y = {}" 
  shows "Domain R \<inter> X \<inter> Y = {}"
using assms by auto

section {* paste *}

text {* the union of two binary relations @{term P} and @{term Q}, where pairs from @{term Q}
  override pairs from @{term P} when their first components coincide *}
definition paste (infix "+*" 75)
where "P +* Q = (P outside Domain Q) \<union> Q"
(* Avoids possible conflicts btw P & Q using `outside', 
thus giving precedence to Q. This is particularly useful when 
P, Q are functions, and one wants to preserve that property. *)

text {* If a relation @{term P} is a subrelation of another relation @{term Q} on @{term Q}'s
  domain, pasting @{term Q} on @{term P} is the same as forming their union. *}
lemma paste_subrel: assumes "P || Domain Q \<subseteq> Q" shows "P +* Q = P \<union> Q"
unfolding paste_def using assms outside_union_restrict by blast

text {* Pasting two relations with disjoint domains is the same as forming their union. *}                                                                                                
lemma paste_disj_domains: assumes "Domain P \<inter> Domain Q = {}" shows "P +* Q = P \<union> Q"
unfolding paste_def Outside_def
using assms
by fast

text {* A relation @{term P} is equivalent to pasting its restriction to some set @{term X} on 
  @{term "P outside X"}. *}
lemma paste_outside_restrict: "P = (P outside X) +* (P || X)"
proof -
  have "Domain (P outside X) \<inter> Domain (P || X) = {}"
    unfolding Outside_def restrict_def by fast
  moreover have "P = P outside X \<union> P || X" by (rule outside_union_restrict)
  ultimately show ?thesis using paste_disj_domains by metis
qed

text {* Pasting @{term Q} on @{term P} yields a right-unique relation if @{term Q} is 
  right-unique, and @{term P} is right-unique outside @{term Q}'s domain. *}
lemma runiq_paste1:
  fixes P::"('a \<times> 'b) set"
    and Q::"('a \<times> 'b) set"
  assumes "runiq Q"
      and "runiq (P outside Domain Q)" (is "runiq ?PoutsideQ")
  shows "runiq (P +* Q)"
proof -
  have paste_sub: "P +* Q \<subseteq> (Q \<union> ?PoutsideQ)" unfolding paste_def by simp
  have "Domain Q \<inter> Domain ?PoutsideQ = {}"
    using outside_reduces_domain by (metis Diff_disjoint)
  with assms have "runiq (Q \<union> ?PoutsideQ)" by (rule disj_Un_runiq)
  then show ?thesis using paste_sub by (rule subrel_runiq)
qed

text {* Pasting two right-unique relations yields a right-unique relation. *}
corollary runiq_paste2:
  assumes "runiq Q"
      and "runiq P" 
shows "runiq (P +* Q)"
using assms runiq_paste1 subrel_runiq
by (metis Diff_subset Outside_def)

text {* Pasting a singleton relation on some other right-unique relation @{term R} yields a
  right-unique relation if the single element of the singleton's domain is not yet in the 
  domain of @{term R}. *}
lemma runiq_paste3:
  assumes "runiq R"
      and "x \<notin> Domain R" 
  shows "runiq (R +* {(x, y)})"
using assms runiq_paste2 runiq_singleton_rel by metis

text {* The domain of two pasted relations equals the union of their domains. *}
lemma paste_Domain: "Domain (P +* Q) = Domain P \<union> Domain Q"
unfolding paste_def Outside_def by blast

text {* Pasting two relations yields a subrelation of their union. *}
lemma paste_sub_Un: "P +* Q \<subseteq> P \<union> Q"
unfolding paste_def Outside_def by fast

text {* The range of two pasted relations is a subset of the union of their ranges. *}
lemma paste_Range: "Range (P +* Q) \<subseteq> Range P \<union> Range Q"
using paste_sub_Un by blast

section {* Converse *}

text {* The definition of @{const converse} isn't suitable for generating code, so we provide
  a code equation using an alternative definition. *}
lemma [code_unfold]: "converse R = { (y, x) . (x, y) \<in> R }" by (rule converse_unfold)

text {* If two relations are subrelations of each other, so are their converse relations. *}
lemma converse_subrel: assumes "P \<subseteq> Q" shows "P\<inverse> \<subseteq> Q\<inverse>"
using assms by fast

text {* The domain of the inverse of a relation is the relation's range. *}
lemma Domain_conv_Range: "Domain (R\<inverse>)=Range R"
by simp

text {* alternative characterisation of the intersection of a relation's domain with some set, in
  terms of the converse relation *}
lemma Domain_Int_wrt_converse: "Domain R \<inter> X \<subseteq> R\<inverse> `` (R `` X)"
by fast

text {* The inverse image of the image of a singleton set under some relation is the same
  singleton set, if both the relation and its converse are right-unique and the singleton set
  is in the relation's domain. *}
lemma converse_Image_singleton_Domain:
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R\<inverse>)"
      and domain: "x \<in> Domain R"
shows "R\<inverse> `` R `` {x} = {x}"
proof -
  have sup: "{x} \<subseteq> R\<inverse> `` R `` {x}" using Domain_Int_wrt_converse domain by fast
  have "trivial (R `` {x})" using runiq domain by (metis runiq_def trivial_singleton)
  then have "trivial (R\<inverse> `` R `` {x})"
    using assms
    by (metis Image_runiq_eq_eval RelationProperties.eval_rel.simps runiq_wrt_eval_rel trivial_def)
  then show ?thesis
    using sup by (metis singleton_sub_trivial_uniq subset_antisym trivial_def)
qed

text {* The inverse image of the image of a singleton set under some relation is the same
  singleton set or empty, if both the relation and its converse are right-unique. *}
lemma converse_Image_singleton:
  assumes "runiq R"
      and "runiq (R\<inverse>)"
  shows "R\<inverse> `` R `` {x} \<subseteq> {x}"
using assms converse_Image_singleton_Domain
by (metis Image_empty Image_within_domain' empty_subsetI set_eq_subset)

text {* The inverse image of the image of a set under some relation is a subset of that set,
  if both the relation and its converse are right-unique. *}
lemma converse_Image: 
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R\<inverse>)"
shows "R\<inverse> `` R `` X \<subseteq> X"
proof -
  have "(R O R\<inverse>) `` X = (\<Union>x \<in> X . (R O R\<inverse>) `` {x})" by (rule Image_eq_UN)
  also have "\<dots> = (\<Union>x\<in>X. R\<inverse> `` R `` {x})" by blast
  also have "\<dots> \<subseteq> (\<Union>x \<in> X. {x})" using converse_Image_singleton assms by fast
  also have "\<dots> = X" by simp
  finally show ?thesis by fast
qed

text {* The inverse statement of @{thm disj_Image_imp_disj_Domain} holds when both the 
  relation and its converse are right-unique. *}
lemma disj_Domain_imp_disj_Image: assumes "Domain R \<inter> X \<inter> Y = {}" 
  assumes "runiq R"
      and "runiq (R\<inverse>)"
  shows "R `` X \<inter> R `` Y = {}"
proof -
  let ?X_on_Dom = "Domain R \<inter> X"
  let ?Y_on_Dom = "Domain R \<inter> Y"
  have "R\<inverse> `` (R `` ?X_on_Dom) \<subseteq> ?X_on_Dom" using converse_Image assms by fast
  moreover have "R\<inverse> `` (R `` ?Y_on_Dom) \<subseteq> ?Y_on_Dom" using converse_Image assms by metis
  ultimately have "R\<inverse> `` R `` ?X_on_Dom \<inter> R\<inverse> `` R `` ?Y_on_Dom \<subseteq> {}" using assms by blast
  moreover have "?X_on_Dom \<inter> ?Y_on_Dom = {}" using assms by blast
  ultimately
  have "{} = Domain (R\<inverse>) \<inter> R `` ?X_on_Dom \<inter> R `` ?Y_on_Dom"
    using disj_Image_imp_disj_Domain by fast
  also have "\<dots> = Range R \<inter> R `` ?X_on_Dom \<inter> R `` ?Y_on_Dom" using Domain_conv_Range by metis
  also have "\<dots> = R `` ?X_on_Dom \<inter> R `` ?Y_on_Dom" by blast
  finally show ?thesis by auto
qed

text {* The converse relation of two pasted relations is right-unique, if 
  the relations have disjoint domains and ranges, and if their converses are both
  right-unique. *}
lemma runiq_converse_paste:
  assumes runiq_P_conv: "runiq (P\<inverse>)"
      and runiq_Q_conv: "runiq (Q\<inverse>)"
      and disj_D: "Domain P \<inter> Domain Q = {}"
      and disj_R: "Range P \<inter> Range Q = {}"
  shows "runiq ((P +* Q)\<inverse>)"
proof -
  have "P +* Q = P \<union> Q" using disj_D by (rule paste_disj_domains)
  then have "(P +* Q)\<inverse> = P\<inverse> \<union> Q\<inverse>" by auto
  also have "\<dots> = P\<inverse> +* Q\<inverse>" using disj_R paste_disj_domains Domain_conv_Range by metis
  finally show ?thesis using runiq_P_conv runiq_Q_conv runiq_paste2 by auto
qed

text {* The converse relation of a singleton relation pasted on some other relation @{term R} is right-unique,
  if the singleton pair is not in @{term "Domain R \<times> Range R"}, and if @{term "R\<inverse>"} is right-unique. *}
lemma runiq_converse_paste_singleton:
  assumes runiq: "runiq (R\<inverse>)" 
      and y_notin_R: "y \<notin> Range R"
      and x_notin_D: "x \<notin> Domain R"
  shows "runiq ((R +* {(x,y)})\<inverse>)"
proof -
  have "{(x,y)}\<inverse> = {(y,x)}" by fastforce
  then have "runiq ({(x,y)}\<inverse>)" using runiq_singleton_rel by metis
  moreover have "Domain R \<inter> Domain {(x,y)} = {}" and "Range R \<inter> (Range {(x,y)})={}"
    using y_notin_R x_notin_D by simp_all
  ultimately show ?thesis using runiq runiq_converse_paste by blast
qed

section {* Injective functions *}

text {* the set of all injective functions from @{term X} to @{term Y} *}
definition injections :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set set"
where "injections X Y = {R . Domain R = X \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"

text {* Given a relation @{term R}, an element @{term x} of the relation's domain type and
  a set @{term Y} of the relation's range type, this function constructs the list of all 
  superrelations of @{term R} that extend @{term R} by a pair @{term "(x,y)"} for some
  @{term y} not yet covered by @{term R}. *}
fun sup_rels_from_alg :: "('a \<times> 'b\<Colon>linorder) set \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set list"
where 
"sup_rels_from_alg R x Y = [ R +* {(x,y)} . y \<leftarrow> sorted_list_of_set (Y - Range R) ]"
(* Y or Y-Range R ? *)

text {* set-based variant of @{const sup_rels_from_alg} *}
definition sup_rels_from :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set set"
where "sup_rels_from R x Y = { R +* {(x, y)} | y . y \<in> Y - Range R }"

text {* On finite sets, @{const sup_rels_from_alg} and @{const sup_rels_from} are equivalent. *}
lemma sup_rels_from_paper_equiv_alg:
  assumes "finite Y"
  shows "set (sup_rels_from_alg R x Y) = sup_rels_from R x Y"
proof -
  have "distinct (sorted_list_of_set (Y - Range R))" using assms by simp
  then have "set [ R +* {(x,y)} . y \<leftarrow> sorted_list_of_set (Y - Range R) ] = { R +* {(x,y)} | y . y \<in> set (sorted_list_of_set (Y - Range R)) }"
    using list_comp_eq_set_comp by simp
  moreover have "set (sorted_list_of_set (Y - Range R)) = Y - Range R" using assms by simp
  ultimately show ?thesis unfolding sup_rels_from_def by simp
qed

text {* the list of all injective functions (represented as relations) from one set 
  (represented as a list) to another set *}
fun injections_alg :: "'a list \<Rightarrow> 'b\<Colon>linorder set \<Rightarrow> ('a \<times> 'b) set list"
where "injections_alg [] Y = [{}]" |
      "injections_alg (x # xs) Y = concat [ sup_rels_from_alg R x Y . R \<leftarrow> injections_alg xs Y ]"
(* We need this as a list in order to be able to iterate over it.  It would be easy to provide 
   an alternative of type ('a \<times> 'b) set set, by using \<Union> and set comprehension. *)

lemma injections_paste:
  assumes new: "x \<notin> A"
  shows "injections (insert x A) Y = (\<Union> { sup_rels_from P x Y | P . P \<in> injections A Y })"
proof (rule equalitySubsetI)
  fix R
  assume "R \<in> injections (insert x A) Y"
  then have injections_unfolded: "Domain R = insert x A \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)"
    unfolding injections_def by simp
  then have Domain: "Domain R = insert x A"
        and Range: "Range R \<subseteq> Y"
        and runiq: "runiq R"
        and runiq_conv: "runiq (R\<inverse>)" by simp_all

  let ?P = "R outside {x}"
  have subrel: "?P \<subseteq> R" unfolding Outside_def by fast
  have subrel_conv: "?P\<inverse> \<subseteq> R\<inverse>" using subrel by blast
  have Domain_pre: "Domain ?P = A"
    using Domain new and outside_reduces_domain
    by (metis Diff_insert_absorb)
  moreover have "Range ?P \<subseteq> Y"
    using Range and outside_union_restrict
    by (metis Int_absorb1 Range_Un_eq inf_sup_ord(3) le_inf_iff)
  moreover have "runiq ?P" using runiq subrel by (rule subrel_runiq)
  moreover have "runiq (?P\<inverse>)" using runiq_conv subrel_conv by (rule subrel_runiq)
  ultimately have P_inj: "?P \<in> injections A Y"
    unfolding injections_def by (metis (lifting, full_types) mem_Collect_eq)

  obtain y where y: "R `` {x} = {y}" using Image_runiq_eq_eval Domain runiq by (metis insertI1)
  from y Range have "y \<in> Y" by fast
  moreover have "y \<notin> Range ?P"
  proof
    assume assm: "y \<in> Range ?P"
    then obtain x' where x'_Domain: "x' \<in> Domain ?P" and x'_P_y: "(x', y) \<in> ?P" by fast
    have x'_img: "x' \<in> R\<inverse> `` {y}" using subrel x'_P_y by fast
    have x_img: "x \<in> R\<inverse> `` {y}" using y by fast
    have "x' \<noteq> x"
    proof -
      from x'_Domain have "x' \<in> A" using Domain_pre by fast
      with new show ?thesis by fast
    qed
    have "trivial (R\<inverse> `` {y})" using runiq_conv runiq_alt by metis
    then have "x' = x" using x'_img x_img by (rule trivial_imp_no_distinct)
    with `x' \<noteq> x` show False ..
  qed
  ultimately have y_in: "y \<in> Y - Range ?P" by (rule DiffI)

  from y have 0: "R || {x} = {(x, y)}" unfolding restrict_def by blast
  then have Dom_restrict: "Domain (R || {x}) = {x}" by simp
  from 0 have 1: "?P +* {(x, y)} = ?P \<union> R || {x}" by (metis outside_union_restrict paste_outside_restrict)
  from Dom_restrict Domain_pre new have "Domain ?P \<inter> Domain (R || {x}) = {}" by simp
  then have "?P +* (R || {x}) = ?P \<union> (R || {x})" by (rule paste_disj_domains)
  then have P_paste: "?P +* {(x, y)} = R" by (metis "1" outside_union_restrict)

  from P_inj y_in P_paste have "\<exists> P \<in> injections A Y . \<exists> y \<in> Y - Range P . R = P +* {(x, y)}" by blast
  (* intermediate step that makes it easier to understand:
  then have "\<exists> P \<in> injections A Y . R \<in> { P +* {(x, y)} | y . y \<in> Y - Range P }" by blast
  *)
  then have "\<exists> Q \<in> { sup_rels_from P x Y | P . P \<in> injections A Y } . R \<in> Q"
    unfolding sup_rels_from_def by auto
  then show "R \<in> \<Union> { sup_rels_from P x Y | P . P \<in> injections A Y }"
    using Union_member by (rule rev_iffD1) (* TODO CL: in an earlier version, Nitpick found spurious counterexamples here and in the step before, possibly because of underspecification. *)
next
  fix R
  assume "R \<in> \<Union> { sup_rels_from P x Y | P . P \<in> injections A Y }"
  then have "\<exists> Q \<in> { sup_rels_from P x Y | P . P \<in> injections A Y } . R \<in> Q"
    using Union_member by (rule rev_iffD2)
  then obtain P and y where P: "P \<in> injections A Y" and y: "y \<in> Y - Range P" and R: "R = P +* {(x, y)}"
    unfolding sup_rels_from_def by auto
  then have P_unfolded: "Domain P = A \<and> Range P \<subseteq> Y \<and> runiq P \<and> runiq (P\<inverse>)"
    unfolding injections_def by (simp add: CollectE)
  then have Domain_pre: "Domain P = A"
        and Range_pre: "Range P \<subseteq> Y"
        and runiq_pre: "runiq P"
        and runiq_conv_pre: "runiq (P\<inverse>)" by simp_all
  have Domain: "Domain R = insert x A" using Domain_pre R outside_reduces_domain paste_def by (metis Domain_empty Domain_insert Un_commute insert_Diff_single insert_is_Un)
  moreover have Range: "Range R \<subseteq> Y" using Range_pre R y paste_Range by (smt Diff_partition Range_empty Range_insert Un_iff insertE subsetD subsetI sup_bot_right)
  moreover have runiq: "runiq R" using runiq_pre R by (metis runiq_paste2 runiq_singleton_rel)
  moreover have runiq_conv: "runiq (R\<inverse>)" using runiq_conv_pre R y new runiq_converse_paste_singleton by (metis DiffE Domain_pre)
  ultimately show "R \<in> injections (insert x A) Y" unfolding injections_def by (metis (lifting, full_types) mem_Collect_eq)
qed

text {* The paper-like definition @{const injections} and the algorithmic definition 
  @{const injections_alg} are equivalent. *}
theorem injections_equiv:
  fixes xs::"'a list"
    and Y::"'b\<Colon>linorder set"
  assumes non_empty: "card Y > 0"
  shows "distinct xs \<Longrightarrow> (set (injections_alg xs Y)::('a \<times> 'b) set set) = injections (set xs) Y"
proof (induct xs)
  case Nil
  have "set (injections_alg [] Y) = {{}::('a \<times> 'b) set}" by simp
  also have "\<dots> = injections (set []) Y"
  proof -
    have "{{}} = {R::(('a \<times> 'b) set) . Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}" (is "?LHS = ?RHS")
    proof
      have "Domain {} = {}" by simp
      moreover have "Range {} \<subseteq> Y" by simp
      moreover have runiq_emptyrel: "runiq {}" using runiq_def trivial_empty runiq_trivial_rel by fast
      moreover have "runiq ({}\<inverse>)" using runiq_emptyrel by (metis (full_types) Domain_empty Range_converse Range_empty_iff)
      ultimately have "Domain {} = {} \<and> Range {} \<subseteq> Y \<and> runiq {} \<and> runiq ({}\<inverse>)" by blast
      (* CL: Merging the steps before and after this comment considerably increases complexity. *)
      then have "{} \<in> {R . Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}" by (rule CollectI)
      then show "?LHS \<subseteq> ?RHS" by (smt empty_subsetI insert_subset)
    next
      {
        fix R
        (* CL: ignoring warning "Introduced fixed type variable(s)"; adding type annotations breaks transitive chain (reported to Isabelle list 2013-09-07) *)
        assume "R \<in> {R::(('a \<times> 'b) set) . Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"
        then have "Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)" ..
        then have "R = {}" using Domain_empty_iff by metis
        then have "R \<in> {{}}" by simp
      }
      then show "?RHS \<subseteq> ?LHS" by (rule subsetI)
    qed
    also have "\<dots> = injections {} Y"
      unfolding injections_def ..
    also have "\<dots> = injections (set []) Y" by simp
    finally show ?thesis .
  qed
  finally show ?case .
next
  case (Cons x xs)

  from non_empty have "finite Y" by (rule card_ge_0_finite)
  (* needed for the longer, more easily comprehensible variant given below *)
  (*
  from Cons.prems have "x \<notin> set xs" by simp
  have insert: "set (x # xs) = insert x (set xs)" by force
  *)

  (* short variant: *)
  have "set (injections_alg (x # xs) Y) = (\<Union> { set (sup_rels_from_alg R x Y) | R . R \<in> injections (set xs) Y })"
    using Cons.hyps Cons.prems by (simp add: image_Collect_mem)
  (* longer, more easily comprehensible variant: *)
  (*
  have "set (injections_alg (x # xs) Y) = set (concat [ sup_rels_from_alg R x Y . R \<leftarrow> injections_alg xs Y ])" by simp
  also have "\<dots> = (\<Union> set (map set [ sup_rels_from_alg R x Y . R \<leftarrow> injections_alg xs Y ]))" by simp
  also have "\<dots> = (\<Union> set ` (set [ sup_rels_from_alg R x Y . R \<leftarrow> injections_alg xs Y ]))" by simp
  also have "\<dots> = (\<Union> set ` ((\<lambda> R . sup_rels_from_alg R x Y) ` set (injections_alg xs Y)))" by simp
  also have "\<dots> = (\<Union> set ` ((\<lambda> R . sup_rels_from_alg R x Y) ` (injections (set xs) Y)))" using Cons.hyps Cons.prems by auto
  also have "\<dots> = (\<Union> set ` { sup_rels_from_alg R x Y | R . R \<in> injections (set xs) Y })" by (simp add: image_Collect_mem)
  also have "\<dots> = (\<Union> { set (sup_rels_from_alg R x Y) | R . R \<in> injections (set xs) Y })" by (simp add: image_Collect_mem)
  *)
  also have "\<dots> = (\<Union> { sup_rels_from R x Y | R . R \<in> injections (set xs) Y })"
    using `finite Y` sup_rels_from_paper_equiv_alg by fast
  (* short variant: *)
  also have "\<dots> = injections (set (x # xs)) Y" using Cons.prems by (simp add: injections_paste)
  (* longer, more easily comprehensible variant: *)
  (*
  also have "\<dots> = injections (insert x (set xs)) Y" using `x \<notin> set xs` by (simp add: injections_paste)
  also have "\<dots> = injections (set (x # xs)) Y" using insert by simp
  *)
  finally show ?case .
qed

(* TODO CL: Maybe introduce a variant of injections that can also generate partial functions.
   This would have to be done by recursing not just to "xs", but to all sublists of "x # xs" of length n - 1. *)

(* TODO CL: check how much of the following we still need *)
section {* Christoph's old stuff *}

definition left_total_on :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool"
where "left_total_on R A \<longleftrightarrow> (\<forall> x \<in> A . \<exists> y . (x, y) \<in> R)"

definition function_on :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool"
where "function_on R A \<longleftrightarrow> left_total_on R A \<and> runiq R"

fun as_part_fun :: "('a \<times> 'b) set \<Rightarrow> 'a \<rightharpoonup> 'b"
where "as_part_fun R a = (let im = R `` {a} in 
        if card im = 1 then Some (the_elem im)
        else None)"

fun eval_rel_or :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
where "eval_rel_or R a z = (let im = R `` {a} in if card im = 1 then the_elem im else z)"

definition to_relation :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) set"
(* the domain can be possibly specified in a separate step, e.g. through || *)
where "to_relation f = {(x, f x) | x . True}"

definition injective :: "('a \<times> 'b) set \<Rightarrow> bool"
where "injective R \<longleftrightarrow> (\<forall> a \<in> Domain R . \<forall> b \<in> Domain R . R `` {a} = R `` {b} \<longrightarrow> a = b)"
(* MC: for the moment, we've used runiq inverse R, reusing existing definitions,
instead of this. *)

lemma "runiq R \<Longrightarrow> runiq (R \<inverse>) \<Longrightarrow> injective R"
proof -
  assume runiq: "runiq R"
  assume runiq_conv: "runiq (R \<inverse>)"
  {
    fix a assume a_Dom: "a \<in> Domain R"
    fix b assume b_Dom: "b \<in> Domain R"
    have "R `` {a} = R `` {b} \<longrightarrow> a = b"
    proof
      assume eq_Im: "R `` {a} = R `` {b}"
      from runiq a_Dom obtain Ra where Ra: "R `` {a} = {Ra}" by (metis Image_runiq_eq_eval runiq)
      from runiq b_Dom obtain Rb where Rb: "R `` {b} = {Rb}" by (metis Image_runiq_eq_eval runiq)
      from eq_Im Ra Rb have eq_Im': "Ra = Rb" by simp
      from eq_Im' Ra a_Dom runiq_conv have a': "(R \<inverse>) `` {Ra} = {a}" by (metis converse_Image_singleton_Domain runiq)
      from eq_Im' Rb b_Dom runiq_conv have b': "(R \<inverse>) `` {Rb} = {b}" by (metis converse_Image_singleton_Domain runiq)
      from eq_Im' a' b' show "a = b" by (metis the_elem_eq)
    qed
  }
  then show ?thesis unfolding injective_def by blast
qed

end
