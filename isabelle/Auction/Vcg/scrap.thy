



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


(*
CL: Keeping old initial vector-based bid implementation (suitable for multiple items per good and
  fractions of items) for reference.
		
(* one participant's bid on a set of goods *)
definition b :: "participant \<Rightarrow> goods \<Rightarrow> nat" where "b i y = (\<Sum> x \<in> y . x)"

text{* convenience type synonyms for most of the basic concepts we are dealing with *}
type_synonym endowment = "nat vector" (* conceptually: good \<Rightarrow> quantity *)
type_synonym endowment_subset = "nat vector" (* conceptually the same, but \<le> endowment *)

(* A single participant ascribes real values to subsets of the endowment. *)
type_synonym valuation = "endowment_subset \<Rightarrow> real"
type_synonym valuations = "valuation vector"
type_synonym bid = "endowment_subset \<Rightarrow> real"

(* A well-formed bid is non-negative for each “subset” of the endowment, i.e. each vector s
   that is component-wise 0 \<le> s \<le> x0. *)
definition bid :: "bid \<Rightarrow> goods \<Rightarrow> endowment \<Rightarrow> bool"
  where "bid b K x0 \<longleftrightarrow> (\<forall> s . non_negative_real_vector K s \<and> vector_le K s x0 \<longrightarrow> b s \<ge> 0)"

type_synonym allocation = "participant \<Rightarrow> endowment_subset"

type_synonym payments = "real vector"
*)

(*
notepad
begin
  fix Rs::"('a \<times> 'b) set set"
  fix Sss::"'a set set"
  fix P::"'a set \<Rightarrow> ('a \<times> 'b) set set"
  (* TODO CL: an example (to be mentioned in the paper) for how hard set theory is for Isabelle:
     takes several minutes to find (2013), 104 ms to prove 
     MC: substituted smt with blast in view of afp submission; however, I think CL's comment above still applies. *)
  have "{ R . \<exists> Y \<in> Sss . R \<in> P Y } = \<Union> { P Y | Y . Y \<in> Sss }" 
  using Collect_cong Union_eq mem_Collect_eq by blast
end
*)


(*abbreviation "strictCovers G == Union -` {G}"*)
(*
abbreviation "partitionsUniverse' == {P-{{}}| P. \<Inter>P \<in> {\<Union>P,{}} }"
abbreviation "partitionsUniverse'' == {P-{{}}| P. \<forall> Q \<subseteq> P. \<Inter>Q \<in> {\<Union>Q,{}} }"
abbreviation "partitionsUniverse''' == {P-{{}}| P. \<forall> Q \<subseteq> P. (Q \<noteq> {} & card Q \<noteq> 1) \<longrightarrow> \<Inter>Q={}}"
abbreviation "partitionsUniverse'''' == {P-{{}}| P. \<forall> Q \<in> Pow P - {{}}. card Q \<noteq> 1 \<longrightarrow>  \<Inter>Q={} }"
abbreviation "partitionsUniverse''''' == {P-{{}}| P. \<forall> Q \<subseteq> P. card Q \<noteq> 1 \<longrightarrow> \<Inter>Q={}}"
*)
(*lemma lm01a: "partitionsUniverse \<subseteq>  {P-{{}}| P. \<Inter>P \<in> {\<Union>P,{}}}" unfolding is_non_overlapping_def by auto
*)


(* theorem assumes "distinct X" shows "set (injectionsAlg X Y)=injections (set X) (set Y)"
proof -
let ?P="\<lambda> L. (distinct L \<longrightarrow> (set (injectionsAlg L Y)=injections (set L) (set Y)))" 
have "?P []" by (simp add: Universes.lm24 lm44) 
moreover have "\<forall>x xs. ?P xs \<longrightarrow> ?P (x#xs)" by (metis distinct.simps(2) list.simps(15) lm86)
ultimately have "?P X" by (rule structInduct)
thus ?thesis using assms by presburger
qed
*)
(* text {* The range of two pasted relations is a subset of the union of their ranges. *}
lemma paste_Range: "Range (P +* Q) \<subseteq> Range P \<union> Range Q"
(* TODO CL: report bug that structured proof found by auto sledgehammer doesn't work *)
using paste_sub_Un by blast

*)
