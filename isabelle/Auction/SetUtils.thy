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

header {* Additional material that we would have expected in Set.thy *}

theory SetUtils
imports Set
begin

text {* An inference rule that combines @{text Set.equalityI} and @{text Set.subsetI} to a single step *}
lemma equalitySubsetI: "(\<And>x . x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x . x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B" by fast

text {* an equivalent notation for the image of a set, using set comprehension *}
lemma image_Collect_mem: "{ f x | x . x \<in> S } = f ` S" by auto

text {* The image of a union is the union of images. *}
lemma image_union: "f ` (X \<union> Y) = f ` X \<union> f ` Y" by auto

end
