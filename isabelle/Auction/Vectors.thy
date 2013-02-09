(*
$Id$

Auction Theory Toolbox

Authors:
* Manfred Kerber <m.kerber@cs.bham.ac.uk>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory Vectors
imports Real

begin

section{* Preliminaries *}

text{* some types defined for our convenience *}
type_synonym bool_vector = "nat \<Rightarrow> bool"
  (* TODO CL: report jEdit bug that suggested completions for nat (\<nat>) and bool (\<bool>) cause syntax errors *)
type_synonym real_vector = "nat \<Rightarrow> real"


subsection{* some range checks for vectors *}

text{* To help the prover in some situations, we introduce a predicate for the range of participants. *}
definition in_range ::
  "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "in_range n i \<equiv> 1 \<le> i \<and> i \<le> n"

text{* we could also, in a higher-order style, generally define a vector whose components satisfy a predicate, and then parameterise this predicate with $\geq 0$ and $> 0$ *}
definition non_negative_real_vector ::
  "nat \<Rightarrow> real_vector \<Rightarrow> bool" where
  "non_negative_real_vector n v \<equiv> \<forall> i::nat . i \<in> {1..n} \<longrightarrow> v i \<ge> 0"

definition positive_real_vector ::
  "nat \<Rightarrow> real_vector \<Rightarrow> bool" where
  "positive_real_vector n v \<equiv> \<forall> i::nat . i \<in> {1..n} \<longrightarrow> v i > 0"

section{* Deviation from a vector *}

text{* We define a function that modifies a vector by using an alternative value for a given component. *}
definition deviation ::
  "nat \<Rightarrow> real_vector \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real_vector" where
  "deviation n bid alternative_value index j \<equiv> if j = index then alternative_value else bid j"

text{* We define a function that,
  given one vector and an alternative one (in practice these will be strategy profiles), and a participant index i,
  returns a vector that
  has component i changed to the alternative value (i.e. in practice: the bid of participant i changed), whereas the others keep their original values.

  Actually this definition doesn't check whether its arguments are non-negative real vectors (i.e. well-formed strategy profiles). *}
(* NOTE CL: I changed the order of arguments compared to our original Theorema attempts, as I think this one is more intuitive.
   TODO CL: ask whether there a way of writing the alternative as b_hat, as it looks in the paper version?
   TODO CL: discuss whether there any useful way we could use n for range-checking?  Or don't we need n at all? *)
definition deviation_vec ::
  "nat \<Rightarrow> real_vector \<Rightarrow> real_vector \<Rightarrow> nat \<Rightarrow> real_vector" where
  "deviation_vec n bid alternative_vec index \<equiv> deviation n bid (alternative_vec index) index"
  (* the old component-wise definition had an error actually:
     "deviation_vec n bid alternative_vec index j \<equiv> deviation n bid (alternative_vec j) index j"
                                                                                     ^^ should have been index
     so actually a component-wise definition was not necessary
     the error didn't cause trouble because of the "j = index" condition in deviation_def,
     but it prevented us from rewriting deviation_def into deviation without providing a component index, i.e. in curried form.
     The latter was desired after introducing remaining_maximum_invariant
       (which uses the more general "deviation" form instead of "deviation_vec") *)


text{* constructing a new vector from a given one, by skipping one component *}
definition skip_index ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "skip_index vector index = (\<lambda> i::nat . vector (if i < index then i else Suc i))"

text{* skipping one component in a non-negative vector keeps it non-negative *}
(* TODO CL: discuss whether we should actually prove the more general lemma that
   skipping one component in a vector whose components each satisfy p still satisfies p (for a suitable p) *)
lemma skip_index_keeps_non_negativity :
  fixes n::nat and v::real_vector and i::nat
  assumes non_empty: "n > 0"
    and non_negative: "non_negative_real_vector n v"
    and range: "i \<in> {1..n}"
  shows "non_negative_real_vector (n-(1::nat)) (skip_index v i)"
proof -
  {
    fix j::nat
    assume j_range: "j \<in> {1..n-(1::nat)}"
    have "(skip_index v i) j \<ge> 0"
    proof (cases "j < i")
      case True
      then have "(skip_index v i) j = v j" unfolding skip_index_def by simp
      with j_range non_negative show ?thesis
        unfolding non_negative_real_vector_def
        by (auto simp add: leD less_imp_diff_less not_leE)
    next
      case False
      then have "(skip_index v i) j = v (Suc j)" unfolding skip_index_def by simp
      with j_range non_negative show ?thesis
        unfolding non_negative_real_vector_def
        by (auto simp add: leD less_imp_diff_less not_leE)
    qed
  }
  then show "non_negative_real_vector (n-(1::nat)) (skip_index v i)" unfolding non_negative_real_vector_def by simp
qed

text{* when two vectors differ in one component, skipping that component makes the vectors equal *}
lemma equal_by_skipping :
  fixes n::nat and v::real_vector and w::real_vector and j::nat and k::nat
  assumes non_empty: "n > 0"
    and j_range: "j \<in> {1..n}"
    and equal_except: "\<forall>i::nat . i \<in> {1..n} \<and> i \<noteq> j \<longrightarrow> v i = w i"
    and k_range: "k \<in> {1..n-(1::nat)}"
  shows "skip_index v j k = skip_index w j k"
proof (cases "k < j")
  case True
  then have "skip_index v j k = v k" 
    "skip_index w j k = w k"
    unfolding skip_index_def by auto
  with equal_except k_range True show ?thesis by auto
next
  case False
  then have "skip_index v j k = v (Suc k)"
   "skip_index w j k = w (Suc k)"
    unfolding skip_index_def by auto
  with equal_except k_range False show ?thesis by auto
qed

end
