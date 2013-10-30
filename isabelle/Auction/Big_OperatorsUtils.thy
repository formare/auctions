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

(* TODO CL: document *)
lemma Max_Im_ge_other_Im1:
  fixes f::"'a \<Rightarrow> 'b\<Colon>linorder"
  assumes "finite A"
      and "\<exists> x \<in> A . f x \<ge> Max (f ` B)"
  shows "Max (f ` A) \<ge> Max (f ` B)"
using assms
by (metis Max_Im_ge dual_order.trans)

(* TODO CL: document *)
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

(* TODO CL: document *)
lemma Max_Im_ge_other_Im2:
  fixes f::"'a \<Rightarrow> 'b\<Colon>linorder"
  assumes finiteA: "finite A"
      and finiteB: "finite B"
      and B_non_empty: "B \<noteq> {}"
      and witness: "\<exists> x \<in> A . \<forall> y \<in> B . f x \<ge> f y"
  shows "Max (f ` A) \<ge> Max (f ` B)"
proof -
  from witness obtain x where *: "x \<in> A" and **: "\<forall> y \<in> B . f x \<ge> f y" by blast
  from finiteB B_non_empty obtain y where "y \<in> B" and "Max (f ` B) = f y" by (rule Max_Im_imp_ex_elem)
  then have "f x \<ge> Max (f ` B)" using ** by fastforce
  then have "\<exists> x \<in> A . f x \<ge> Max (f ` B)" using * by blast
  with finiteA show ?thesis by (rule Max_Im_ge_other_Im1)
qed

end

