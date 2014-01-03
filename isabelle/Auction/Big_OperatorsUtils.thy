(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Christoph Lange <math.semantic.web@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* Additional material that we would have expected in Big_Operators.thy *}

theory Big_OperatorsUtils
imports
  Main
  
begin

section {* sum of a function over a set *}

lemma setsum_restrict_fun_zero:
  fixes A::"'a set"
    and S::"'a set"
    and f::"'a \<Rightarrow> 'b"
    and g::"'b \<Rightarrow> 'c\<Colon>{zero,comm_monoid_add}"
    and z::'b
  assumes finite: "finite S"
      and zero: "g z = 0"
  shows "(\<Sum> x \<in> S . g (if x \<in> A then f x else z)) = (\<Sum> x \<in> S \<inter> A . g (f x))"
(* TODO CL: Sledgehammer in Isabelle2013-1-RC2 doesn't find a proof given default timeout. *)
proof -
  have "(\<Sum> x \<in> S . g (if x \<in> A then f x else z)) = (\<Sum> x \<in> S . if x \<in> A then g (f x) else 0)"
    using zero by (metis (hide_lams, full_types))
  also have "\<dots> = (\<Sum> x \<in> S \<inter> A . g (f x))"
    using finite by (rule setsum_restrict_set[symmetric])
  finally show ?thesis .
qed

text {* a variant of @{thm setsum_restrict_fun_zero} for the case that @{term g} also depends on
  @{term "x \<in> S"} *}
lemma setsum_restrict_fun_zero':
  fixes A::"'a set"
    and S::"'a set"
    and f::"'a \<Rightarrow> 'b"
    and g::"'a \<Rightarrow> 'b \<Rightarrow> 'c\<Colon>{zero,comm_monoid_add}"
    and z::'b
  assumes finite: "finite S"
      and zero: "\<forall> x \<in> S . g x z = 0"
  shows "(\<Sum> x \<in> S . g x (if x \<in> A then f x else z)) = (\<Sum> x \<in> S \<inter> A . g x (f x))"
using assms setsum_restrict_fun_zero
by (smt setsum.cong setsum_restrict_set)

text {* A variant of @{thm setsum_cong2} that's easier to apply in certain contexts *}
lemma setsum_cong2':
  assumes "\<forall> x \<in> S . f x = g x"
  shows "(\<Sum> x \<in> S . f x) = (\<Sum> x \<in> S . g x)"
by (metis assms setsum_cong2)

section {* maximum *}

(* TODO CL: document *)
lemma Max_Im_ge:
  fixes f::"'a \<Rightarrow> 'b\<Colon>linorder"
  assumes "finite A"
      and "x \<in> A"
  shows "Max (f ` A) \<ge> f x"
using assms by simp

text {* For any function, a finite, non-empty set has an element on which the function reaches its maximum. *}
lemma Max_Im_imp_ex_elem:
  assumes "finite A"
      and "A \<noteq> {}"
  obtains x where "x \<in> A" and "Max (f ` A) = f x"
(* This takes 232 ms in Isabelle2013-1-RC3:
   using assms by (metis (hide_lams, no_types) Max_in all_not_in_conv finite_imageI image_iff)
*)
proof -
  from `finite A` have "finite (f ` A)" by (rule finite_imageI)
  moreover have "f ` A \<noteq> {}" using `A \<noteq> {}` by simp
  ultimately have "Max (f ` A) \<in> f ` A" by (rule Max_in)
  then have "\<exists> x \<in> A . Max (f ` A) = f x" using image_iff by blast
  then show ?thesis by (metis that) (* TODO CL: ask what "that" is *)
qed

text {* Assume a finite set @{term A} and a finite, non-empty set @{term B}.
  Suppose that for any element of @{term B} there exists an element of @{term A},
  for which a given function returns a greater or equal value.
  Then, the maximum of this function on @{term A} is greater or equal its maximum on @{term B}. *}
lemma Max_Im_ge_other_Im:
  fixes f::"'a \<Rightarrow> 'b\<Colon>linorder"
  assumes finiteA: "finite A"
      and finiteB: "finite B"
      and B_non_empty: "B \<noteq> {}"
      and witnesses: "\<forall> y \<in> B . \<exists> x \<in> A . f x \<ge> f y"
  shows "Max (f ` A) \<ge> Max (f ` B)"
proof -
  from finiteB B_non_empty obtain y where "y \<in> B" and "Max (f ` B) = f y" by (rule Max_Im_imp_ex_elem)
  with witnesses obtain x where "x \<in> A" and *: "f x \<ge> Max (f ` B)" by fastforce
  from finiteA `x \<in> A` have "Max (f ` A) \<ge> f x" by (rule Max_Im_ge)
  with * show ?thesis by (rule order.trans)
qed

lemma Max_Im_ge_lower_bound:
  assumes "\<forall> x \<in> S . f x \<ge> z"
      and "finite S"
      and "S \<noteq> {}"
  shows "Max (f ` S) \<ge> z"
using assms
by (metis Max_Im_imp_ex_elem)

end

