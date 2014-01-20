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

header {* Sums of functions, that involve relations, over a set *}

theory SumsInvolvingRelations
imports
  RelationProperties
  
begin

text {* For summing over the pairs in a right-unique relation it is sufficient to sum over the 
  domain of the relation. *}
lemma setsum_Domain_runiq_rel:
  fixes R::"('a \<times> 'b) set"
    and f::"'a \<Rightarrow> 'b \<Rightarrow> 'c\<Colon>{comm_monoid_add}"
  assumes "runiq R"
  shows "(\<Sum> x \<in> Domain R . f x (THE y . (x, y) \<in> R)) = (\<Sum> (x, y) \<in> R . f x y)"
proof -
  (* TODO CL: manually optimise some metis invocations. *)
  have "inj_on fst R"
    by (smt assms inj_onI runiq_basic surjective_pairing)
  moreover have "Domain R = fst ` R"
    by (metis fst_eq_Domain)
    (* CL: in Isabelle2013-1-RC3, metis is faster than force here *)
  moreover have "\<And> tup . tup \<in> R \<Longrightarrow> f (fst tup) (snd tup) = f (fst tup) (THE y . (fst tup, y) \<in> R)" 
    by (smt calculation(1) inj_onD prod.inject surjective_pairing the_equality)
  ultimately have "(\<Sum> x \<in> Domain R . f x (THE y . (x, y) \<in> R)) = (\<Sum> tup \<in> R . f (fst tup) (snd tup))"
    by (rule setsum_reindex_cong)
  also have "\<dots> = (\<Sum> (x, y) \<in> R . f x y)" by (simp add: split_beta')
  finally show ?thesis .
qed

text {* For summing over the pairs in a relation whose converse is right-unique,
  it is sufficient to sum over the range of the relation. *}
lemma setsum_Range_runiq_conv_rel:
  fixes R::"('a \<times> 'b) set"
    and f::"'a \<Rightarrow> 'b \<Rightarrow> 'c\<Colon>comm_monoid_add"
  assumes "runiq (R\<inverse>)"
  shows "(\<Sum> y \<in> Range R . f (THE x . (x, y) \<in> R) y) = (\<Sum> (y, x) \<in> R\<inverse> . f x y)"
proof -
  def g \<equiv> "\<lambda> x y . f y x"
  have "(\<Sum> y \<in> Range R . f (THE x . (x, y) \<in> R) y) = (\<Sum> y \<in> Domain (R\<inverse>) . f (THE x . (x, y) \<in> R) y)"
    by (metis Domain_converse)
  also have "\<dots> = (\<Sum> y \<in> Domain (R\<inverse>) . f (THE x . (y, x) \<in> R\<inverse>) y)"
  proof -
    {
      fix x y
      have "(x, y) \<in> R \<longleftrightarrow> (y, x) \<in> R\<inverse>" by simp
      then have "(THE x . (x, y) \<in> R) = (THE x . (y, x) \<in> R\<inverse>)" by (metis converse_iff)
    }
    then show ?thesis by presburger
  qed
  also have "\<dots> = (\<Sum> y \<in> Domain (R\<inverse>) . g y (THE x . (y, x) \<in> R\<inverse>))" unfolding g_def by fast
  also have "\<dots> = (\<Sum> (y, x) \<in> R\<inverse> . g y x)" using assms by (rule setsum_Domain_runiq_rel)
  also have "\<dots> = (\<Sum> (y, x) \<in> R\<inverse> . f x y)" unfolding g_def by fast
  finally show ?thesis .
qed

text {* When both a relation and its converse are right-unique, it does not make a difference
  whether a sum runs over the first components or the second components of each pair in 
  the relation. *}
lemma setsum_Domain_Range_runiq_rel:
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R\<inverse>)"
  shows "(\<Sum> x \<in> Domain R . f x (THE y . (x, y) \<in> R)) = (\<Sum> y \<in> Range R . f (THE x . (x, y) \<in> R) y)"
proof -
  have "(\<Sum> x \<in> Domain R . f x (THE y . (x, y) \<in> R)) = (\<Sum> (x, y) \<in> R . f x y)"
    using runiq by (rule setsum_Domain_runiq_rel)
  also have "\<dots> = (\<Sum> (y, x) \<in> R\<inverse> . f x y)" by (rule setsum_rel_comm)
  also have "\<dots> = (\<Sum> y \<in> Range R . f (THE x . (x, y) \<in> R) y)" using runiq_conv by (rule setsum_Range_runiq_conv_rel[symmetric])
  finally show ?thesis .
qed

lemma
  assumes "y \<notin> A"
  shows "(\<Sum> x \<in> A . f ((R \<union> {(y, z)}) ,, x)) = (\<Sum> x \<in> A . f (R ,, x))"
sorry

end

