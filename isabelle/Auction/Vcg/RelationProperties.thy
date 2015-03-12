(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Additional properties of relations, and operators on relations,
  as they have been defined by Relations.thy *}

theory RelationProperties
imports
  Main
  RelationOperators
  SetUtils
  Conditionally_Complete_Lattices (*cSup_singleton*)

begin

section {* right-uniqueness *}

(* flip is applied to pairs so that (flip (x, y)) = (y, x) *)
lemma injflip: "inj_on flip A" by (metis flip_flip inj_on_def)

lemma lm003: "card P = card (P^-1)" using assms card_image flip_conv injflip by metis

lemma nn56: "(card X = 1) = (X={the_elem X})" 
by (metis One_nat_def card_Suc_eq card_empty empty_iff the_elem_eq)

lemma lm007b: "trivial X = (X={} \<or> card X=1)" using 
nn56 order_refl subset_singletonD trivial_def trivial_empty by (metis(no_types))

lemma lm004: "trivial P = trivial (P^-1)" using trivial_def subset_singletonD 
subset_refl subset_insertI nn56 converse_inject converse_empty lm003 by metis

(* The range of P restricted to X is equal to the image of X through P *)
lemma lll85: "Range (P||X) = P``X" unfolding restrict_def by blast

lemma lll02:  "((P || X) || Y) = (P || (X \<inter> Y))" 
unfolding restrict_def by fast

lemma ll41: "Domain (R||X) = Domain R \<inter> X" using restrict_def by fastforce

text {* A subrelation of a right-unique relation is right-unique. *}
lemma subrel_runiq: assumes "runiq Q" "P \<subseteq> Q" shows "runiq P" 
using assms runiq_def by (metis Image_mono subsetI trivial_subset)

lemma lll31: assumes "runiq P" shows "inj_on fst P" 
unfolding inj_on_def using assms runiq_def trivial_def trivial_imp_no_distinct 
the_elem_eq surjective_pairing subsetI Image_singleton_iff by (metis(no_types))

text {* alternative characterization of right-uniqueness: the image of a singleton set is
   @{const trivial}, i.e.\ an empty or a singleton set. *}
lemma runiq_alt: "runiq R \<longleftrightarrow> (\<forall> x . trivial (R `` {x}))" 
unfolding runiq_def using Image_empty lm007 the_elem_eq by (metis(no_types))
 
text {* an alternative definition of right-uniqueness in terms of @{const eval_rel} *}
(* Note that R `` {x} is the image of {x} under R and R ,, x gives you an element y such that R x y. Because of right-uniqueness in this case the element is determined, otherwise it may be undetermined *)
lemma runiq_wrt_eval_rel: "runiq R = (\<forall>x . R `` {x} \<subseteq> {R ,, x})" by (metis eval_rel.simps runiq_alt trivial_def)

lemma l31: assumes "runiq f" assumes "(x,y)\<in>f" shows "y=f,,x" using 
assms runiq_wrt_eval_rel subset_singletonD Image_singleton_iff equals0D singletonE by fast

lemma runiq_basic: "runiq R \<longleftrightarrow> (\<forall> x y y' . (x, y) \<in> R \<and> (x, y') \<in> R \<longrightarrow> y = y')" 
unfolding runiq_alt lm01 by blast

lemma ll71: assumes "runiq f" shows "f``(f^-1``Y) \<subseteq> Y" 
using assms runiq_basic ImageE converse_iff subsetI by (metis(no_types))

lemma ll68: assumes "runiq f" "y1 \<in> Range f" shows 
"(f^-1 `` {y1} \<inter> f^-1 `` {y2} \<noteq> {}) = (f^-1``{y1}=f^-1``{y2})"
using assms ll71 by fast

lemma converse_Image: 
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R^-1)"
shows "(R^-1) `` R `` X \<subseteq> X" using assms by (metis converse_converse ll71)

lemma lll32: assumes "inj_on fst P" shows "runiq P" unfolding runiq_basic 
using assms fst_conv inj_on_def old.prod.inject by (metis(no_types))

(* Another characterization of runiq, relating the set theoretical expression P to the injectivity of the function fst applied to P *)
lemma lll33: "(runiq P) = (inj_on fst P)" using lll31 lll32 by blast

lemma disj_Un_runiq: assumes "runiq P" "runiq Q" "(Domain P) \<inter> (Domain Q) = {}" shows "runiq (P \<union> Q)" 
using assms lll33 fst_eq_Domain lm010b by metis

lemma runiq_paste1: assumes "runiq Q" "runiq (P outside Domain Q)" shows "runiq (P +* Q)"
unfolding paste_def using assms disj_Un_runiq Diff_disjoint Un_commute outside_reduces_domain
by (metis (poly_guards_query))

corollary runiq_paste2: assumes "runiq Q" "runiq P" shows "runiq (P +* Q)"
using assms runiq_paste1 subrel_runiq Diff_subset Outside_def by (metis)

(* Let f be a function, then its graph {(x, f x)} and all its restrictions such that P x for arbitrary P are right-unique. *)
lemma l14: "runiq {(x,f x)| x. P x}" unfolding runiq_basic by fast

lemma lm013: assumes "x \<in> Domain R" "runiq R" shows "card (R``{x})=1"
using assms  lm007b 
DomainE Image_singleton_iff empty_iff
by (metis runiq_alt)


text {* The image of a singleton set under a right-unique relation is a singleton set. *}
lemma Image_runiq_eq_eval: assumes "x \<in> Domain R" "runiq R" shows "R `` {x} = {R ,, x}" 
using assms lm013 by (metis eval_rel.simps nn56)

lemma lm022: assumes "trivial f" shows "runiq f" 
using assms lm01 runiq_basic snd_conv by fastforce

text {* A singleton relation is right-unique. *}
corollary runiq_singleton_rel: "runiq {(x, y)}" using trivial_singleton lm022 by fast

text {* The empty relation is right-unique *}
lemma runiq_emptyrel: "runiq {}" using trivial_empty lm022 by blast

(* characterization of right-uniqueness with  \<exists>! *)
lemma runiq_wrt_ex1:
  "runiq R \<longleftrightarrow> (\<forall> a \<in> Domain R . \<exists>! b . (a, b) \<in> R)"
using runiq_basic by (metis Domain.DomainI Domain.cases)

text {* alternative characterization of the fact that, if a relation @{term R} is right-unique,
  its evaluation @{term "R,,x"} on some argument @{term x} in its domain, occurs in @{term R}'s
  range. Note that we need runiq R in order to get a definite value for @{term "R,,x"} *}
lemma eval_runiq_rel:
  assumes domain: "x \<in> Domain R"
      and runiq: "runiq R" 
  shows "(x, R,,x) \<in> R"
using assms by (metis l31 runiq_wrt_ex1)

text {* Evaluating a right-unique relation as a function on the relation's domain yields an
  element from its range. *}
lemma eval_runiq_in_Range:
  assumes "runiq R"
      and "a \<in> Domain R"
  shows "R ,, a \<in> Range R"
using assms by (metis Range_iff eval_runiq_rel)










subsection {* converse *}

text {* The inverse image of the image of a singleton set under some relation is the same
  singleton set, if both the relation and its converse are right-unique and the singleton set
  is in the relation's domain. *}
lemma converse_Image_singleton_Domain:
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R\<inverse>)"
      and domain: "x \<in> Domain R"
shows "R\<inverse> `` R `` {x} = {x}"
proof -
  have sup: "{x} \<subseteq> R\<inverse> `` R `` {x}" using domain by fast
  have "trivial (R `` {x})" using runiq domain by (metis runiq_def trivial_singleton)
  then have "trivial (R\<inverse> `` R `` {x})"
    using assms runiq_def by blast
  then show ?thesis
    using sup by (metis singleton_sub_trivial_uniq subset_antisym trivial_def)
qed

text {* The images of two disjoint sets under an injective function are disjoint. *}

lemma disj_Domain_imp_disj_Image: assumes "Domain R \<inter> X \<inter> Y = {}" 
  assumes "runiq R"
      and "runiq (R\<inverse>)"
  shows "(R `` X) \<inter> (R `` Y) = {}" 
using assms unfolding runiq_basic by blast

lemma runiq_converse_paste_singleton: assumes "runiq (P^-1)" "y\<notin>(Range P)" 
shows "runiq ((P +* {(x,y)})\<inverse>)" (is "?u (?P^-1)")
proof -
have "(?P) \<subseteq> P \<union> {(x,y)}" using assms by (metis paste_sub_Un)
then have "?P^-1 \<subseteq> P^-1 \<union> ({(x,y)}^-1)" by blast
moreover have "... = P^-1 \<union> {(y,x)}" by fast
moreover have "Domain (P^-1) \<inter> Domain {(y,x)} = {}" using assms(2) by auto
ultimately moreover have "?u (P^-1 \<union> {(y,x)})" using assms(1) by (metis disj_Un_runiq runiq_singleton_rel)
ultimately show ?thesis by (metis subrel_runiq)
qed










section {* injectivity *}
(*
text {* A relation @{term R} is injective on its domain iff any two domain elements having the same image
  are equal.  This definition on its own is of limited utility, as it does not assume that @{term R}
  is a function, i.e.\ right-unique. *}
definition injective :: "('a \<times> 'b) set \<Rightarrow> bool"
where "injective R \<longleftrightarrow> (\<forall> a \<in> Domain R . \<forall> b \<in> Domain R . R `` {a} = R `` {b} \<longrightarrow> a = b)"

text {* If both a relation and its converse are right-unique, it is injective on its domain. *}
lemma runiq_and_conv_imp_injective: 
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R \<inverse>)"
  shows "injective R"
proof -
  {
    fix a assume a_Dom: "a \<in> Domain R"
    fix b assume b_Dom: "b \<in> Domain R"
    have "R `` {a} = R `` {b} \<longrightarrow> a = b"
    proof
      assume eq_Im: "R `` {a} = R `` {b}"
      from runiq a_Dom obtain Ra where Ra: "R `` {a} = {Ra}" by (metis Image_runiq_eq_eval)
      from runiq b_Dom obtain Rb where Rb: "R `` {b} = {Rb}" by (metis Image_runiq_eq_eval)
      from eq_Im Ra Rb have eq_Im': "Ra = Rb" by simp
      from eq_Im' Ra a_Dom runiq_conv have a': "(R \<inverse>) `` {Ra} = {a}"
        using converse_Image_singleton_Domain runiq by metis
      from eq_Im' Rb b_Dom runiq_conv have b': "(R \<inverse>) `` {Rb} = {b}"
        using converse_Image_singleton_Domain runiq by metis
      from eq_Im' a' b' show "a = b" by simp
    qed
  }
  then show ?thesis unfolding injective_def by blast
qed
*)
text {* The following is a classical definition of the set of all injective functions from @{term X} to @{term Y}. *}
definition injections :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set set"
where "injections X Y = {R . Domain R = X \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"
(*
text {* introduction rule that establishes the injectivity of a relation *}
lemma injectionsI:
  fixes R::"('a \<times> 'b) set"
  assumes "Domain R = X"
      and "Range R \<subseteq> Y"
      and "runiq R"
      and "runiq (R\<inverse>)"
  shows "R \<in> injections X Y"
using assms unfolding injections_def using CollectI by blast

text {* the set of all injective partial functions (including total ones) from @{term X} to @{term Y}. *}
definition partial_injections :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set set"
where "partial_injections X Y = {R . Domain R \<subseteq> X \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"

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
  then have "set [ R +* {(x,y)} . y \<leftarrow> sorted_list_of_set (Y - Range R) ] = { R +* {(x,y)} | y . y \<in> set (sorted_list_of_set (Y - Range R)) }"    by auto
  moreover have "set (sorted_list_of_set (Y - Range R)) = Y - Range R" using assms by simp
  ultimately show ?thesis unfolding sup_rels_from_def by simp
qed
*)
text {* The following definition is a constructive (computational) characterization of the set of all injections X Y, represented by a list. That is, we define the list of all injective functions (represented as relations) from one set (represented as a list) to another set. We formally prove the equivalence of the constructive and the classical definition in Universes.thy. *}
fun injections_alg :: "'a list \<Rightarrow> 'b\<Colon>linorder set \<Rightarrow> ('a \<times> 'b) set list"
where "injections_alg [] Y = [{}]" |
      "injections_alg (x # xs) Y = concat [ [ R +* {(x,y)} . y \<leftarrow> sorted_list_of_set (Y - Range R) ]
      . R \<leftarrow> injections_alg xs Y ]"
(* We need this as a list in order to be able to iterate over it.  It would be easy to provide 
   an alternative of type ('a \<times> 'b) set set, by using \<Union> and set comprehension. *)
(*
text {* the set-theoretic variant of the recursive rule of @{const injections_alg} *}
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

  (* We need to establish this fact in a reusable way. *)
  from Domain new have Domain_pre: "Domain ?P = A" by (rule Domain_outside_singleton)
  have P_inj: "?P \<in> injections A Y"
  proof (rule injectionsI)
    show "Domain ?P = A" by (rule Domain_pre)
    show "Range ?P \<subseteq> Y" using Range by (rule Range_outside_sub)
    show "runiq ?P" using runiq subrel by (rule subrel_runiq)
    show "runiq (?P\<inverse>)" using runiq_conv subrel_conv by (rule subrel_runiq)
  qed

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
    have "trivial (R\<inverse> `` {y})" using runiq_conv by (metis runiq_alt)
    then have "x' = x" using x'_img x_img by (rule trivial_imp_no_distinct)
    with `x' \<noteq> x` show False ..
  qed
  ultimately have y_in: "y \<in> Y - Range ?P" by (rule DiffI)

  from y have x_rel: "R || {x} = {(x, y)}" unfolding restrict_def by blast
  from x_rel have Dom_restrict: "Domain (R || {x}) = {x}" by simp
  from x_rel have P_paste': "?P +* {(x, y)} = ?P \<union> R || {x}"
    using outside_union_restrict paste_outside_restrict by metis
  from Dom_restrict Domain_pre new have "Domain ?P \<inter> Domain (R || {x}) = {}" by simp
  then have "?P +* (R || {x}) = ?P \<union> (R || {x})" by (rule paste_disj_domains)
  then have P_paste: "?P +* {(x, y)} = R" using P_paste' outside_union_restrict by blast

  from P_inj y_in P_paste have "\<exists> P \<in> injections A Y . \<exists> y \<in> Y - Range P . R = P +* {(x, y)}" by blast
  (* intermediate step that makes it easier to understand:
  then have "\<exists> P \<in> injections A Y . R \<in> { P +* {(x, y)} | y . y \<in> Y - Range P }" by blast
  *)
  then have "\<exists> Q \<in> { sup_rels_from P x Y | P . P \<in> injections A Y } . R \<in> Q"
    unfolding sup_rels_from_def by auto
  then show "R \<in> \<Union> { sup_rels_from P x Y | P . P \<in> injections A Y }"
    using Union_member by (rule rev_iffD1)
next
  fix R
  assume "R \<in> \<Union> { sup_rels_from P x Y | P . P \<in> injections A Y }"
  then have "\<exists> Q \<in> { sup_rels_from P x Y | P . P \<in> injections A Y } . R \<in> Q"
    using Union_member by (rule rev_iffD2)
  then obtain P and y where P: "P \<in> injections A Y"
                        and y: "y \<in> Y - Range P"
                        and R: "R = P +* {(x, y)}"
    unfolding sup_rels_from_def by auto
  then have P_unfolded: "Domain P = A \<and> Range P \<subseteq> Y \<and> runiq P \<and> runiq (P\<inverse>)"
    unfolding injections_def by (simp add: CollectE)
  then have Domain_pre: "Domain P = A"
        and Range_pre: "Range P \<subseteq> Y"
        and runiq_pre: "runiq P"
        and runiq_conv_pre: "runiq (P\<inverse>)" by simp_all

  show "R \<in> injections (insert x A) Y"
  proof (rule injectionsI)
    show "Domain R = insert x A"
    proof -
      have "Domain R = Domain P \<union> Domain {(x,y)}" using paste_Domain R by metis
      also have "\<dots> = A \<union> {x}" using Domain_pre by simp
      finally show ?thesis by auto
    qed

    show "Range R \<subseteq> Y"
    proof -
      have "Range R \<subseteq> Range P \<union> Range {(x,y)} \<and> Range P \<union> Range {(x,y)} \<subseteq> Y \<union> {y}"
        using paste_Range R Range_pre by force
      then show ?thesis using y by auto
    qed

    show "runiq R"
      using runiq_pre R runiq_singleton_rel runiq_paste2 by fast

    show "runiq (R\<inverse>)"
      using runiq_conv_pre R y new and runiq_converse_paste_singleton DiffE Domain_pre
      by metis
  qed
qed

text {* There are finitely many injective function from a finite set to another finite set. *}
lemma finite_injections:
  fixes X::"'a set"
    and Y::"'b set"
  assumes "finite X"
      and "finite Y"
  shows "finite (injections X Y)"
proof (rule rev_finite_subset)
  from assms show "finite (Pow (X \<times> Y))" by simp
  moreover show "injections X Y \<subseteq> Pow (X \<times> Y)"
  proof
    fix R assume "R \<in> (injections X Y)"
    then have "Domain R = X \<and> Range R \<subseteq> Y" unfolding injections_def by simp
    then have "R \<subseteq> X \<times> Y" by fast
    then show "R \<in> Pow (X \<times> Y)" by simp
  qed
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
      have "Domain {} = {}" by (rule Domain_empty)
      moreover have "Range {} \<subseteq> Y" by simp
      moreover note runiq_emptyrel
      moreover have "runiq ({}\<inverse>)" by (simp add: runiq_emptyrel)
      ultimately have "Domain {} = {} \<and> Range {} \<subseteq> Y \<and> runiq {} \<and> runiq ({}\<inverse>)" by blast
      (* CL: Merging the steps before and after this comment considerably increases complexity. *)
      then have "{} \<in> {R . Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}" by (rule CollectI)
      then show "?LHS \<subseteq> ?RHS" using empty_subsetI insert_subset by fast
    next
      show "?RHS \<subseteq> ?LHS"
      proof
        fix R
        assume "R \<in> {R::(('a \<times> 'b) set) . Domain R = {} \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"
        then show "R \<in> {{}}" by (simp add: Domain_empty_iff)
      qed
    qed
    also have "\<dots> = injections (set []) Y"
      unfolding injections_def by simp
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
*)


lemma Image_within_domain': fixes x R shows "(x \<in> Domain R) = (R `` {x} \<noteq> {})" by blast

end




(* abbreviation "mylog n == (if (n \<noteq> 0) then (Discrete.log n) else (-1))"
abbreviation "Card X == mylog (card (Pow X))"

lemma assumes "finite X" shows "Card X = card X" (is "?L=?R") using assms 
proof -
have "Card X=Discrete.log (card (Pow X))" using assms by auto
moreover have "... = Discrete.log (2^card X)" using assms by (metis (poly_guards_query) card_Pow)
ultimately show ?thesis by fastforce
qed

lemma assumes "\<not> (finite X)" shows "Card X=-1" using assms by simp
*)

(* lemma "Domain ((a outside (X \<union> {i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) ) 
\<subseteq> Domain a - X \<union> {i}" using assms Outside_def by auto

lemma "(R - ((X\<union>{i})\<times>(Range R))) = (R outside X) outside {i}" using Outside_def 
by (metis l37a)

lemma "{(i, x)} - {(i,y)} = {i} \<times> ({x}-{y})" by fast
*)


(* lemma "swap = curry \<circ> (((swap (op \<circ>)) flip) \<circ> split)" using lm29 sledgehammer[provers=z3] *)

(* lemma "finite=(swap (op \<in>))(range set)" unfolding lm46 using lm45b by blast *)
