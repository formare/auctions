theory Scraps2

imports Main "../StrictCombinatorialAuction" "../MiscTools" "../Universes"
"../UniformTieBreaking"

begin

lemma lm07: assumes "isChoice (graph {winningAllocationsRel N G b} t)" shows 
"t (winningAllocationsRel N G b) \<in> winningAllocationsRel N G b" 
using assms
proof - (* MC: to be cleaned *)
let ?W="winningAllocationsRel N G b" let ?T="graph {?W} t" let ?TT="graph UNIV t" let ?TTT="Graph t"
have "?T``{?W} \<subseteq> ?W" using assms by fast
moreover have "?TTT``{?W} = (?TTT || {?W})``{?W}" using restrict_def Image_def by fast
moreover have "?TTT || {?W} = ?TT || {?W}" using ll36 by metis
moreover have "... = ?T" using lm05 by (metis Int_UNIV_left)
moreover have "?T``{?W} = ?TTT``{?W}" using lm06 by (metis calculation(2))
moreover have "?T``{?W} \<subseteq> t`{?W}" using l4 by (metis calculation(5) subsetI)
ultimately show ?thesis using assms by (metis (hide_lams, no_types) image_eqI insertI1 l4 set_rev_mp)
qed

corollary lm53b: assumes "condition1 (b::_ => real) i"  "a \<in> possibleAllocationsRel N G" 
"i\<in>N-{n}" "n \<in> Domain a" "finite N" "finite G"
shows
"alpha N G b n \<ge> setsum b (a -- n)" (is "?L \<ge> ?R") using assms lm53 
proof -
let ?X="{n}" have "Domain a \<inter> ?X \<noteq> {}" using assms by blast
then show "Max ((setsum b)`(possibleAllocationsRel (N-?X) G)) \<ge> setsum b (a outside ?X)" using assms lm53 by metis
qed

lemma lm60: assumes "n \<notin> Domain a" "a \<in> possibleAllocationsRel N G" "finite G" "finite N" shows 
"alpha N G b n \<ge> setsum b (a -- n)"
proof -
let ?a="a -- n" let ?d=Domain have "?a = a" using assms Outside_def by blast
then moreover have "?d ?a \<subseteq> N-{n}" using 
assms(1,2) lm28b by (metis insert_Diff_single subset_insert)
ultimately have "a \<in> possibleAllocationsRel (N-{n}) G" using assms 
by (metis (full_types) lm28b)
then have "setsum b a \<in> (setsum b ` (possibleAllocationsRel (N-{n}) G))"
by blast
moreover have "finite (possibleAllocationsRel (N-{n}) G)" using assms lm59 by (metis finite_Diff)
ultimately show ?thesis using Max.coboundedI
by (metis (hide_lams, no_types) `a -- n = a` finite_imageI)
qed

corollary lm61: (*MC: of lm60 and lm53b*) assumes
"condition1 (b::_ => real) i" 
"a \<in> possibleAllocationsRel N G"
"i\<in>N-{n}"
"finite N"
"finite G"
shows "alpha N G b n \<ge> setsum b (a -- n)" using assms lm53b lm60 by metis

corollary lm61b: assumes "condition1 (b::_ => real) i" "a \<in> winningAllocationsRel N G c" 
"i\<in>N-{n}" "finite N" "finite G" shows "alpha N G b n \<ge> setsum b (a -- n)"  
proof -
have "a \<in> possibleAllocationsRel N G" using assms(2) lm03 by fast
then show ?thesis using assms lm61 by metis
qed

corollary lm61c: assumes "condition1 (b::_ => real) i" "i\<in>N-{n}" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows 
"alpha N G b n \<ge> remainingValueRel N G t b n" (is "?L \<ge> ?R") 
using assms lm03 lm61 lm07 set_rev_mp 
proof -
have "winningAllocationRel N G t b \<in> winningAllocationsRel N G b" 
using assms(5) lm07 by (metis (hide_lams, no_types))
then show ?thesis using lm61b assms by metis
qed

lemma lm62: "(a::real) \<ge> b = (a - b \<ge> 0)" by linarith

(*
lemma lm72b: assumes "t (winningAllocationsRel N G b) \<in> winningAllocationsRel N G b" shows
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))" using assms lm72 
by blast
*)

corollary lm61d: assumes "condition1 (b::_=>real) i" "i\<in>N-{n}" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows "paymentsRel N G t b n \<ge> 0" 
proof - have "alpha N G b n \<ge> remainingValueRel N G t b n" using assms lm61c by metis thus ?thesis using lm62 by simp qed

abbreviation "condition2 b N == EX i1 i2. (i1 \<in> N - {i2} & i2 \<in> N - {i1} & condition1 b i1 & condition1 b i2)"

corollary lm61e:
assumes 
"condition2 (b::_=>real) N" 
"finite N"
"finite G"
"isChoice (graph {winningAllocationsRel N G b} t)"
shows
"paymentsRel N G t b n \<ge> 0"
proof -
  obtain i where 
  0: "condition1 b i & i \<in> N-{n}" using assms(1) by blast
  then have "condition1 b i" by blast moreover have "i \<in> N-{n}" using 0 by fast 
  moreover have "finite N" using assms(2) by simp moreover have "finite G" using assms(3) by auto  
  moreover have "isChoice (graph {winningAllocationsRel N G b} t)" using assms(4) by fast  
  ultimately show ?thesis by (rule lm61d)
qed

abbreviation "monotonebids == condition2"

lemma lm71: fixes N b assumes
"EX i1 i2. i1 \<in> N - {i2} & i2 \<in> N - {i1} & 
(\<forall> t t'. (trivial t & trivial t' & Union t \<subseteq> Union t') \<longrightarrow>
setsum b ({i1}\<times>t) \<le> setsum b ({i1}\<times>t') & setsum b ({i2}\<times>t) \<le> setsum b ({i2}\<times>t'))"
shows "condition2 (b) N" using assms by blast

corollary lm61f: assumes "monotonebids (b::_=>real) N" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel N G b} t)" shows "\<forall>n. paymentsRel N G t b n \<ge> 0"  
proof -
{fix n have "paymentsRel N G t b n \<ge> 0" using assms by (rule lm61e)} then show ?thesis by fastforce
qed

lemma ll59: shows "P O Q={(x,z) | x z. (EX y. (x,y) \<in> P & (y,z)\<in>Q)}"
using assms relcomp_def by blast

lemma ll60: shows "P O Q O R = 
{(v,z)| v z. EX x y. (v,x) \<in> P & (x,y) \<in> Q & (y,z)\<in>R}" by blast

lemma ll88: assumes "P xx" shows "{(x, f x)|x. P x}``{xx} = {f xx}"
using Image_def assms by blast

lemma lll07: "(P \<inter> Q)``{x} = (P``{x} \<inter> (Q``{x}))" by fastforce

lemma assumes "P \<inter> Q={}" shows "P^-1 \<inter> Q^-1={}" using assms by fast

(*
lemma runiq_alt2: "runiq R = (\<forall> x \<in> Domain R. trivial (R `` {x}))" 
by (metis Domain.DomainI Image_singleton_iff lm01 runiq_alt)
*)

(*
text {* the image of a singleton set under a right-unique relation is
   @{const trivial}, i.e.\ an empty or singleton set. *}

text {* If all images of singleton sets under a relation are
   @{const trivial}, i.e.\ an empty or singleton set, the relation is right-unique. *}
   
lemma Image_within_runiq_domain:
  fixes x R
  assumes "runiq R"
  shows "x \<in> Domain R \<longleftrightarrow> (\<exists> y . R `` {x} = {y})" using assms Image_runiq_eq_eval by fast

lemma runiq_imp_singleton_image':
  assumes runiq: "runiq R"
      and dom: "x \<in> Domain R"
  shows "the_elem (R `` {x}) = (THE y . (x, y) \<in> R)" (is "the_elem (R `` {x}) = ?y")
unfolding the_elem_def
using assms Image_singleton_iff Image_within_runiq_domain singletonD singletonI by (metis)

lemma runiq_conv_imp_singleton_preimage':
  assumes runiq_conv: "runiq (R\<inverse>)"
      and ran: "y \<in> Range R"
  shows "the_elem ((R\<inverse>) `` {y}) = (THE x . (x, y) \<in> R)" 
(* CL: using assms runiq_imp_singleton_image' sledgehammer doesn't find a proof within reasonable time
   using Isabelle2013-1-RC3. *)
proof -
  from ran have dom: "y \<in> Domain (R\<inverse>)" by simp
  with runiq_conv have "the_elem ((R\<inverse>) `` {y}) = (THE x . (y, x) \<in> (R\<inverse>))" by (rule runiq_imp_singleton_image')
  also have "\<dots> = (THE x . (x, y) \<in> R)" by simp
  finally show ?thesis .
qed

text {* another alternative definition of right-uniqueness in terms of @{const eval_rel} *}
lemma runiq_wrt_eval_rel':
  fixes R :: "('a \<times> 'b) set"
  shows "runiq R \<longleftrightarrow> (\<forall>x \<in> Domain R . R `` {x} = {R ,, x})" unfolding runiq_wrt_eval_rel by fast
*)

(*
lemma runiq_imp_THE_right_comp:
  fixes a and b
  assumes runiq: "runiq R"
      and aRb: "(a, b) \<in> R"
  shows "b = (THE b . (a, b) \<in> R)" using assms by (metis runiq_basic the_equality)

lemma runiq_imp_THE_right_comp':
  assumes runiq: "runiq R"
      and in_Domain: "a \<in> Domain R"
  shows "(a, THE b. (a, b) \<in> R) \<in> R"
proof -
  from in_Domain obtain b where *: "(a, b) \<in> R" by force
  with runiq have "b = (THE b . (a, b) \<in> R)" by (rule runiq_imp_THE_right_comp)
  with * show ?thesis by simp
qed

lemma THE_right_comp_imp_runiq:
  assumes "\<forall> a b . (a, b) \<in> R \<longrightarrow> b = (THE b . (a, b) \<in> R)"
  shows "runiq R"
using assms DomainE runiq_wrt_ex1 by metis

text {* another alternative definition of right-uniqueness in terms of @{const The} *}
lemma runiq_wrt_THE:
  "runiq R \<longleftrightarrow> (\<forall> a b . (a, b) \<in> R \<longrightarrow> b = (THE b . (a, b) \<in> R))"
proof
  assume "runiq R"
  then show "\<forall> a b . (a, b) \<in> R \<longrightarrow> b = (THE b . (a, b) \<in> R)" by (metis runiq_imp_THE_right_comp)
next
  assume "\<forall> a b . (a, b) \<in> R \<longrightarrow> b = (THE b . (a, b) \<in> R)"
  then show "runiq R" by (rule THE_right_comp_imp_runiq)
qed

lemma runiq_conv_imp_THE_left_comp:
  assumes runiq_conv: "runiq (R\<inverse>)" and aRb: "(a, b) \<in> R"
  shows "a = (THE a . (a, b) \<in> R)"
proof -
  from aRb have "(b, a) \<in> R\<inverse>" by simp
  with runiq_conv have "a = (THE a . (b, a) \<in> R\<inverse>)" by (rule runiq_imp_THE_right_comp)
  then show ?thesis by fastforce
qed

lemma runiq_conv_imp_THE_left_comp':
  assumes runiq_conv: "runiq (R\<inverse>)"
      and in_Range: "b \<in> Range R"
  shows "(THE a. (a, b) \<in> R, b) \<in> R"
proof -
  from in_Range obtain a where *: "(a, b) \<in> R" by force
  with runiq_conv have "a = (THE a . (a, b) \<in> R)" by (rule runiq_conv_imp_THE_left_comp)
  with * show ?thesis by simp
qed

lemma THE_left_comp_imp_runiq_conv:
  assumes "\<forall> a b . (a, b) \<in> R \<longrightarrow> a = (THE a . (a, b) \<in> R)"
  shows "runiq (R\<inverse>)"
proof -
  from assms have "\<forall> b a . (b, a) \<in> R\<inverse> \<longrightarrow> a = (THE a . (b, a) \<in> R\<inverse>)" by auto
  then show ?thesis by (rule THE_right_comp_imp_runiq)
qed

lemma runiq_conv_wrt_THE:
  "runiq (R\<inverse>) \<longleftrightarrow> (\<forall> a b . (a, b) \<in> R \<longrightarrow> a = (THE a . (a, b) \<in> R))"
proof -
  have "runiq (R\<inverse>) \<longleftrightarrow> (\<forall> a b . (a, b) \<in> R\<inverse> \<longrightarrow> b = (THE b . (a, b) \<in> R\<inverse>))" by (rule runiq_wrt_THE)
  also have "\<dots> \<longleftrightarrow> (\<forall> a b . (a, b) \<in> R \<longrightarrow> a = (THE a . (a, b) \<in> R))" by auto
  finally show ?thesis .
qed
*)


(*
text {* right-uniqueness of a restricted relation expressed using basic set theory *}
lemma runiq_restrict: "runiq (R || X) \<longleftrightarrow> (\<forall> x \<in> X . \<forall> y y' . (x, y) \<in> R \<and> (x, y') \<in> R \<longrightarrow> y = y')"
proof -
  have "runiq (R || X) \<longleftrightarrow> (\<forall> x y y' . (x, y) \<in> R || X \<and> (x, y') \<in> R || X \<longrightarrow> y = y')"
    by (rule runiq_basic)
  also have "\<dots> \<longleftrightarrow> (\<forall> x y y' . (x, y) \<in> { p . fst p \<in> X \<and> p \<in> R } \<and> (x, y') \<in> { p . fst p \<in> X \<and> p \<in> R } \<longrightarrow> y = y')"
    using restrict_ext' by blast
  also have "\<dots> \<longleftrightarrow> (\<forall> x \<in> X . \<forall> y y' . (x, y) \<in> R \<and> (x, y') \<in> R \<longrightarrow> y = y')" by auto
  finally show ?thesis .
qed

subsection {* paste *}

text {* Pasting a singleton relation on some other right-unique relation @{term R} yields a
  right-unique relation if the single element of the singleton's domain is not yet in the 
  domain of @{term R}. *}
lemma runiq_paste3:
  assumes "runiq R"
      and "x \<notin> Domain R" 
  shows "runiq (R +* {(x, y)})"
using assms runiq_paste2 runiq_singleton_rel by metis

subsection {* difference *}

text {* Removing one pair from a right-unique relation still leaves it right-unique. *}
lemma runiq_except:
  assumes "runiq R"
  shows "runiq (R - {tup})"
using assms
by (rule subrel_runiq) fast

lemma runiq_Diff_singleton_Domain:
  assumes runiq: "runiq R"
      and in_rel: "(x, y) \<in> R"
  shows "x \<notin> Domain (R - {(x, y)})"
(* TODO CL: optimise manually.  Takes 103 ms in Isabelle2013-1-RC3 *)
using assms DomainE Domain_Un_eq UnI1 Un_Diff_Int member_remove remove_def runiq_wrt_ex1
by metis
*)

(*
text {* The inverse image of the image of a singleton set under some relation is the same
  singleton set or empty, if both the relation and its converse are right-unique. *}
corollary converse_Image_singleton:
  assumes "runiq R"
      and "runiq (R\<inverse>)"
  shows "R\<inverse> `` R `` {x} \<subseteq> {x}"
using assms converse_Image_singleton_Domain by fast
*)

(*
lemma runiq_imp_Dom_rel_Range:
  assumes "x \<in> Domain R"
      and "runiq R"
  shows "(THE y . (x, y) \<in> R) \<in> Range R"
using assms
by (metis Range.intros runiq_imp_THE_right_comp runiq_wrt_ex1)

lemma runiq_conv_imp_Range_rel_Dom:
  assumes y_Range: "y \<in> Range R"
      and runiq_conv: "runiq (R\<inverse>)"
  shows "(THE x . (x, y) \<in> R) \<in> Domain R"
proof -
  from y_Range have "y \<in> Domain (R\<inverse>)" by simp
  then have "(THE x . (y, x) \<in> R\<inverse>) \<in> Range (R\<inverse>)" using runiq_conv by (rule runiq_imp_Dom_rel_Range)
  then show ?thesis by simp
qed
*)

(*
text {* The converse relation of two pasted relations is right-unique, if 
  the relations have disjoint domains and ranges, and if their converses are both
  right-unique. *}
lemma runiq_converse_paste: (* MC: Too strong hypotheses; superseded by ll777b *)
  assumes runiq_P_conv: "runiq (P\<inverse>)"
      and runiq_Q_conv: "runiq (Q\<inverse>)"
      and disj_D: "Domain P \<inter> Domain Q = {}"
      and disj_R: "Range P \<inter> Range Q = {}"
  shows "runiq ((P +* Q)\<inverse>)"
proof -
  have "P +* Q = P \<union> Q" using disj_D by (rule paste_disj_domains)
  then have "(P +* Q)\<inverse> = P\<inverse> \<union> Q\<inverse>" by auto
  also have "\<dots> = P\<inverse> +* Q\<inverse>" using disj_R paste_disj_domains Domain_converse by metis
  finally show ?thesis using runiq_P_conv runiq_Q_conv runiq_paste2 by auto
qed
*)


(*
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
*)

(*
text {* If a relation is known to be right-unique, it is easier to know when we can evaluate it
  like a function, using @{const eval_rel_or}. *}
lemma eval_runiq_rel_or:
  assumes "runiq R"
  shows "eval_rel_or R a z = (if a \<in> Domain R then the_elem (R `` {a}) else z)"
proof -
  from assms have "card (R `` {a}) = 1 \<longleftrightarrow> a \<in> Domain R"
    (* TODO CL: optimise, put into RelationProperties.thy; so far takes 98 ms with Isabelle2013-1-RC2 *)
    using Image_within_runiq_domain card_Suc_eq card_empty ex_in_conv One_nat_def by metis
  then show ?thesis by force
qed
*)


(*
text {* Infrastructure for proving some property of a trivial set by distinguishing the 
  two cases @{text empty} and @{text "singleton x"}. *}
(* CL: thanks to Christian Sternagel and Joachim Breitner
http://stackoverflow.com/questions/18686865/how-can-i-bind-the-schematic-variable-case-in-a-rule-for-proof-by-cases
By "cases pred: trivial" one could enable this rule by default; this would also allow to omit "consumes 1". *)
lemma trivial_cases [case_names empty singleton, consumes 1]:
  assumes "trivial X"
  assumes empty: "X = {} \<Longrightarrow> P"
      and singleton: "\<And> x . X = {x} \<Longrightarrow> P"
  shows "P"
using assms by (auto simp: trivial_def)

(* How to use trivial_cases:
notepad
begin
  fix Q
  fix X::"'a set"
  have "trivial X" sorry (* prove *)
  then have "Q X"
  proof (cases rule: trivial_cases)
    case empty
    then show ?thesis sorry (* prove *)
  next
    case (singleton x)
    then show ?thesis sorry (* prove *)
  qed
end
*)
*)

(*   by (metis equals0D insertE triv trivial_cases x y) *)
(*
proof -
  from triv show "x = y"
  proof (cases rule: trivial_cases)
    case empty
    with x show ?thesis by simp
  next
    case singleton
    with x y show ?thesis by fast
  qed
qed
*)


(*
A = {1,2}
B = {1,3}
A = B - {3} \<union> {2}
*)
(*
(* TODO CL: document *)
lemma Diff_replace:
  assumes A_repl_B: "A = B - {x} \<union> {y}"
      and card_eq: "card B = card A"
      and old_elem: "x \<in> B"
  shows "A - B = {y} - {x}" using assms try0
(* TODO CL: In Isabelle2013-1-RC3, this is hard for Sledgehammer to find.
   Maybe optimise manually. *)
proof cases
  assume "x = y"
  then show ?thesis
    by (metis A_repl_B Diff_cancel Un_insert_right insert_Diff_single insert_absorb old_elem sup_bot_right)
next
  assume "x \<noteq> y"
  with A_repl_B have "A - A \<inter> B = {y}" sorry
oops

This was the proof when when we had assumed B \<subseteq> A, which we are actually not interested in:
using assms
by (metis Diff_cancel Diff_insert_absorb Un_empty_right Un_insert_right insert_iff Set.set_insert set_rev_mp)
*)


(*
lemma Union_map_member:
  assumes "x \<in> \<Union> { f y | y . y \<in> Z }"
  shows "\<exists> y \<in> Z . x \<in> f y"
using assms by fast
*)


(*
text {* Growing, in terms of set union a member @{term x} of a family of sets by a set @{term x'} grows
  the union of all of these sets by @{term x'}. *}
lemma Union_family_grown_member:
  fixes Q::"'a set set"
    and P::"'a set set"
    and A::"'a set"
    and x::"'a set"
    and x'::"'a set"
  assumes grow_member: "Q = P - {x} \<union> {x' \<union> x}"
      and Union_before: "\<Union> P = A - x'"
      and increment_sub_set: "x' \<subseteq> A"
      and old_member_in_family: "x \<in> P"
  shows "\<Union> Q = A"
(* CL: This proof was found by Sledgehammer and cleaned up manually, but it may need further cleanups. *)
(* Sledgehammer once found this alternative (something like 104 ms in Isabelle2013-1-RC3) but now can't find it any more:
by (smt Sup_insert Un_Diff_cancel Un_assoc Un_commute insert_absorb insert_def singleton_conv subset_Un_eq) *)
using assms
proof -
  obtain remove :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
    where remove_def: "\<forall>y S. y \<in> S \<longrightarrow> insert y (remove y S) = S \<and> y \<notin> remove y S"
    using [[metis_new_skolem]] by (metis Set.set_insert)
  have f2: "\<forall>B C D. \<not> B \<union> C \<subseteq> D \<or> D \<union> C = D"
    by auto
  have f3: "\<forall>y S. \<Union>insert y S = \<Union>S \<union> y"
    by auto (* TODO CL: make this a lemma of its own *)

  have f4: "\<Union>insert x' P = A"
    using Union_before increment_sub_set by force
  then have f5: "\<forall>y. \<Union>insert y (insert x' P) = A \<union> y"
    by auto

  have f9: "insert (x \<union> x') (P - {x}) = Q"
    using grow_member by auto
  then have "\<forall>y . y \<in> Q \<or> x \<union> x' \<noteq> y"
    by fastforce
  then have "x \<union> x' \<subseteq> \<Union>Q"
    by (metis Sup_upper)
  then have f13: "\<Union>Q = \<Union>insert x Q"
    using Union_insert by force

  have f12: "insert (x \<union> x') (remove x P) = Q"
    using remove_def f9 old_member_in_family by (metis Diff_insert_absorb)

  have "x \<subseteq> A"
    using f4 old_member_in_family by auto
  moreover have "\<forall>y. \<not> y \<subseteq> A \<or> y \<union> x' \<subseteq> A"
    using increment_sub_set by simp
  ultimately have "x \<union> x' \<subseteq> A"
    by blast
  moreover have "\<forall>y. \<Union>insert x' (insert y P) = A \<union> y"
    using f5 by auto
  moreover have "insert x Q = insert (x \<union> x') P"
    using remove_def f12 old_member_in_family by (metis insert_commute)
  ultimately have "\<Union>insert x' (insert x Q) = A"
    by (metis Un_absorb2)
  moreover have "\<forall>y y'. x \<union> x' \<noteq> y \<or> y \<in> insert y' Q"
    using f9 by fastforce
  ultimately have "\<Union>insert x Q = A"
    using f2 f3 by (metis Sup_upper)
  then show ?thesis
    using f13 by fastforce
qed
*)

text {* A set comprehension formed over a property, which is satisfied by exactly 
  one object, yields a singleton set containing that object. *}
lemma Collect_uniq_prop_singleton:
  assumes "\<exists>! x . P x"
  shows "{ x . P x } = { THE x . P x }"
using assms
(* TODO CL: optimise by some manual steps *)
by (metis (full_types) Collect_cong singleton_conv2 theI')
*)


(* TODO CL: find better name *)
lemma Union_map_compr_eq1:
  fixes x::'a
    and f::"'b \<Rightarrow> 'a set"
    and P::"'b set"
  shows "x \<in> (\<Union> {f Y | Y . Y \<in> P}) \<longleftrightarrow> (\<exists> Y \<in> P . x \<in> f Y)"
(* CL: the following proof takes 2.64s in Isabelle2013-1-RC1:
   by (metis UN_iff Union_set_compr_eq) *)
proof -
  have "x \<in> (\<Union> {f Y | Y . Y \<in> P}) \<longleftrightarrow> x \<in> (\<Union> (f ` P))" by (simp add: image_Collect_mem)
  also have "\<dots> \<longleftrightarrow> (\<exists> y \<in> (f ` P) . x \<in> y)" by (rule Union_iff)
  also have "\<dots> \<longleftrightarrow> (\<exists> y . y \<in> (f ` P) & x \<in> y)" by force
  also have "\<dots> \<longleftrightarrow> (\<exists> y \<in> (f ` P) . x \<in> y)" by blast
  also have "\<dots> \<longleftrightarrow> (\<exists> Y \<in> P . x \<in> (f Y))" by force
  finally show ?thesis .
qed


text {* Two alternative notations for the big union operator involving set comprehension are
  equivalent. *}
lemma Union_set_compr_eq: "(\<Union> x\<in>A . f x) = \<Union> { f x | x . x \<in> A }"
proof (rule equalitySubsetI)
  fix y
  assume "y \<in> (\<Union> x\<in>A . f x)"
  then obtain z where "z \<in> { f x | x . x \<in> A }" and "y \<in> z" by blast
  then show "y \<in> \<Union> { f x | x . x \<in> A }" by (rule UnionI)
next
  fix y
  assume "y \<in> \<Union> { f x | x . x \<in> A }"
  then show "y \<in> (\<Union> x\<in>A . f x)" by force
qed



text {* When a set of elements @{term A} is non-empty, and a function @{term f} returns a non-empty
  set for at least one member of @{term A}, the union of the image of @{term A} under @{term f}
  is non-empty, too. *}
lemma Union_map_non_empty:
  assumes "x \<in> A"
      and "f x \<noteq> {}"
  shows "\<Union> (f ` A) \<noteq> {}"
proof -
  from assms(1) have "f ` A \<noteq> {}" by fast
  with assms show ?thesis by force
qed


lemma card_diff_gt_0:
  assumes "finite B"
      and "card A > card B"
  shows "card (A - B) > 0"
using assms
by (metis diff_card_le_card_Diff le_0_eq neq0_conv zero_less_diff)


section {* Set difference *}

text {* Subtracting a proper subset from a set yields another proper subset. *}
lemma Diff_psubset_is_psubset:
  assumes "A \<noteq> {}"
      and "A \<subset> B"
  shows "B - A \<subset> B"
(* TODO CL: maybe report to Isabelle mailing list: "try" without "using assms" finds a lengthy 
   Sledgehammer proof, so maybe the obvious "using assms" should always be tried first? *)
using assms
by blast

text {* If there exists a unique @{term x} with some property, then the set 
  of all such @{term x} is trivial. *}
lemma ex1_imp_trivial:
  assumes "\<exists>! x . P x"
  shows "trivial { x . P x }"
proof -
  from assms have "\<forall> a b . a \<in> { x . P x } \<and> b \<in> { x . P x } \<longrightarrow> a = b" by blast
  then show ?thesis by (rule no_distinct_imp_trivial)
qed 

(*
      proof
        fix Y assume Y_class: "Y \<in> P \<union> {B}"
        show "X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y"
        proof (*rule case_split_2_times_2*)
          assume "X \<in> P \<and> Y \<in> P"
          then have "X \<in> P" and "Y \<in> P" by simp_all
          with part show ?thesis unfolding is_partition_of_def is_partition_def sorry
        next
          assume "X \<in> P \<and> Y \<notin> P"
          then have "X \<in> P" and "Y \<notin> P" by simp_all
          with Y_class have "Y = B" by fast
          with `X \<in> P` `\<Union> P = A` new have "X \<inter> Y = {}" unfolding is_partition_of_def by blast
          moreover have "X \<noteq> Y" using `X \<in> P` `Y \<notin> P` by fast
          ultimately show ?thesis by auto
        next (* TODO CL: refactor the part that's symmetric to the previous case *)
          assume "X \<notin> P \<and> Y \<in> P"
          then have "X \<notin> P" and "Y \<in> P" by simp_all
          with X_class have "X = B" by fast
          with `Y \<in> P` `\<Union> P = A` new have "X \<inter> Y = {}" unfolding is_partition_of_def by blast
          moreover have "X \<noteq> Y" using `Y \<in> P` `X \<notin> P` by fast
          ultimately show ?thesis by auto
        next
          assume "X \<notin> P \<and> Y \<notin> P"
          then have "X \<notin> P" and "Y \<notin> P" by simp_all
          with X_class Y_class have "X = B" and "Y = B" by simp_all
          with non_empty show ?thesis by simp
        qed
      qed
*)


text {* A finite set has finitely many partitions. *}
lemma finite_all_partitions:
  assumes "finite A"
  shows "finite (all_partitions A)"
unfolding all_partitions_def is_partition_of_def is_partition_def
(* CL: The following takes 74 ms in Isabelle2013-1-RC1:
   by (smt PowD PowI Union_Pow_eq assms finite_Pow_iff in_mono mem_Collect_eq rev_finite_subset subsetI subset_Pow_Union) *)
(* TODO CL: make the following more readable.  It was found by Sledgehammer but even after some cleanup I still fail to understand it. *)
proof
  have "finite (Pow (Pow A))" using assms by simp
  moreover have "{ P . \<Union> P = A } \<subseteq> Pow (Pow A)"
  proof
    fix P assume "P \<in> { P . \<Union> P = A }"
    then show "P \<in> Pow (Pow A)" by blast
  qed
  ultimately have "finite { P . \<Union> P = A }" by (rule rev_finite_subset)
    (* CL: If we start with this, Isabelle2013-1-RC1 finds a fast but exceedingly complex Isar proof. *)
  then show "finite {P . \<Union> P = A} \<or> finite {P. \<forall> X \<in> P . \<forall> Y \<in> P . (X \<inter> Y \<noteq> {}) \<longleftrightarrow> X = Y}" ..
qed


The algorithmic computation of all partitions of a set works as
in the following example:
\begin{itemize}
\item Set: $\{\a}$\\
  Partitions: $\{\{a\}\}$
\item Set: $\{a,b\}$
  Partitions: $\{\{a\}, \{b\}\}, \{\{a, b\}\}$
\item Set: $\{a,b,c\}$
  Partitions: $\{\{a\}, \{b\}, \{c\}\}, \{\{a,b\}, \{c\}\}, \{\{a,c\}, \{b\}\}, \{\{a\}, \{c,b\}\}, \{\{a,b,c\}\}$
\end{itemize}

BTW, the number of partitions of a set (same as the number of equivalence relations on the set) is known as 
\href{http://en.wikipedia.org/wiki/Bell_number}{Bell number}.

text {* Summing over all pairs of a relation is the same as summing over all pairs of the
  converse relation after flipping them. *}
lemma setsum_rel_comm:
  fixes R::"('a \<times> 'b) set"
    and f::"'a \<Rightarrow> 'b \<Rightarrow> 'c\<Colon>comm_monoid_add"
  shows "(\<Sum> (x, y) \<in> R . f x y) = (\<Sum> (y', x') \<in> R\<inverse> . f x' y')"
proof -
  (* TODO CL: manually optimise some metis invocations *)
  have "inj_on flip (R\<inverse>)"
    by (metis flip_flip inj_on_def)
  moreover have "R = flip ` (R\<inverse>)"
    by (metis converse_converse flip_conv)
  moreover have "\<And> tup . tup \<in> R\<inverse> \<Longrightarrow> f (snd tup) (fst tup) = f (fst (flip tup)) (snd (flip tup))"
    by (metis flip_def fst_conv snd_conv)
  ultimately have "(\<Sum> tup \<in> R . f (fst tup) (snd tup)) = (\<Sum> tup \<in> R\<inverse> . f (snd tup) (fst tup))"
    using setsum.reindex_cong by (metis (erased, lifting))
  then show ?thesis
    by (metis (mono_tags) setsum.cong split_beta)
qed


(* CL: probably not needed, neither for close-to-paper nor for computable version
definition possible_allocations_fun :: "goods \<Rightarrow> participant set \<Rightarrow> allocation_fun set"
where "possible_allocations_fun G N = { (Y,x) .
  Y \<in> all_partitions G
  \<and> (\<forall> y \<in> Y . (\<exists> n \<in> N . x y = Some n) \<or> x y = None)
  \<and> inj_on x Y
 }"
*)

(*
section {* Relational vs. predicate form*}

text {* A general combinatorial auction in predicate form.
  To give the auction designer flexibility (including the possibility to introduce mistakes),
  we only constrain the left hand side of the relation, as to cover valid inputs.
  This definition makes sure that whenever we speak of a combinatorial auction, there is a
  valid input on the left hand side.  In other words, this predicate returns false for relations having left
  hand side entries that are known not to be valid inputs.
  For this and other reasons (including Isabelle's difficulties to handle complex set comprehensions)
  it is more convenient to treat the auction as a predicate over all of
  its arguments, instead of a left-hand-side/right-hand-side relation.*}
definition pred :: "goods \<Rightarrow> participant set \<Rightarrow> bids \<Rightarrow> allocation_rel \<Rightarrow> payments \<Rightarrow> bool"
where "pred G N b x p \<longleftrightarrow> valid_input G N b"

text {* Given an auction in predicate form @{const pred}, construct a predicate that takes all 
  arguments of @{const pred} as one @{term "(input, outcome)"} pair, and checks whether its
  components satisfy @{const pred}.  This is useful for modelling the auction in relational form. *}
definition pred_tup :: "combinatorial_auction_pred \<Rightarrow> combinatorial_auction_tup \<Rightarrow> bool"
where "pred_tup P T \<longleftrightarrow> (\<exists> G N b x p . T = ((G, N, b), (x, p)) \<and> P G N b x p)"

text {* We construct the relational form of an auction from the predicate form @{const pred}: given a 
  predicate that defines an auction by telling us for all possible arguments whether they 
  form an @{term "(input, outcome)"} pair according to the auction's definition, we construct a predicate
  that tells us whether all @{term "(input, outcome)"} pairs in a given relation satisfy that predicate,
  i.e.\ whether the given relation is an auction of the desired type. *}
definition rel_sat_pred :: "combinatorial_auction_pred \<Rightarrow> combinatorial_auction_rel \<Rightarrow> bool"
where "rel_sat_pred P A \<longleftrightarrow> (\<forall> T \<in> A . pred_tup P T)"

(* TODO CL: Now that we have rel_all, check whether this is still needed.  rel_sat_pred could also
   now be defined as "A \<subseteq> (rel_all P)" *)
text {* A variant of @{const rel_sat_pred}: We construct a predicate that tells us whether the
  given relation comprises \emph{all} @{term "(input, outcome)"} pairs that satisfy the given auction predicate, 
  i.e.\ whether the given relation comprises all possible auctions of the desired type.  *}
definition rel_all_pred :: "combinatorial_auction_pred \<Rightarrow> combinatorial_auction_rel \<Rightarrow> bool"
where "rel_all_pred P A \<longleftrightarrow> (\<forall> T . T \<in> A \<longleftrightarrow> pred_tup P T)"

(* TODO CL: document *)
definition rel_all :: "combinatorial_auction_pred \<Rightarrow> combinatorial_auction_rel"
where "rel_all P = { T . pred_tup P T }"

(* TODO CL: document *)
lemma pred_imp_rel_all: "P G N b x p \<Longrightarrow> ((G, N, b), (x, p)) \<in> rel_all P"
unfolding rel_all_def
using pred_tup_def mem_Collect_eq
by force
*)



(* CL: probably not needed, neither for close-to-paper nor for computable version
type_synonym allocation_fun = "(goods set) × (goods ? participant)"
*)
(*
type_synonym combinatorial_auction_pred = "goods ? participant set ? bids ? allocation_rel ? payments ? bool"
type_synonym combinatorial_auction_tup = "(goods × participant set × bids) × (allocation_rel × payments)"
type_synonym combinatorial_auction_rel = "combinatorial_auction_tup set"

section {* Valid input *}

type_synonym input_validity = "goods ? participant set ? bids ? bool"

text {* Valid input (i.e.\ valid bids w.r.t.\ the goods and participants).  As we represent
  @{typ bids} as functions, which are always total in Isabelle/HOL, we can't simply test, e.g., whether
  their domain is @{term "G × N"} for the given goods @{term G} and participants @{term N}.  All we 
  can enforce are non-empty finite sets of goods and participants, and that the bids are monotonic
  w.r.t. (sub)sets of goods, and non-negative, with bids on an empty set of goods being zero.

  We need the monotonicity as we do not  *}
(* CL: Once we realise general/special auctions using locales, we need a valid_input axiom. *)
definition valid_input :: "goods ? participant set ? bids ? bool"
where "valid_input G N b ?
  card G > 0 ? card N > 0 ?
  (? n H H' . n ? N ? H ? H' ? b n H ? b n H') (* monotonicity *) ?
  (? n H . n ? N ? H ? G ? b n H ? 0) (* non-negativity *) ?
  (? n ? N . b n {} = 0) (* zero on empty set *)"
*)
section {* Allocations *}
(* 
text {* the value (according to the bids submitted) of a certain allocation *}
fun value_rel :: "bids ? allocation_rel ? price"
where "value_rel b x = (? (y::goods) ? Domain x . b (x ,, y) y
  (* CL@CR: This implicitly assumes a value of 0 for goods not sold.  OK?
            Goods not sold don't occur in the allocation relation x and 
            therefore won't be summands of this sum. *)
)"

(* CL: probably not needed, neither for close-to-paper nor for computable version
definition value_fun :: "bids ? allocation_fun ? price"
where "value_fun b Yp  = (let Y = fst Yp; x = snd Yp in
  ? y ? Y . (let n = x y in 
    case n of None ? 0 (* CL@CR: OK to assume a value of 0 for goods not sold? *)
            | Some n ? b n y))"
*)
*)


end

