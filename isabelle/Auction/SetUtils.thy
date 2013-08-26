(*
$Id$

Auction Theory Toolbox

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

(* TODO give it some name with "image", "Collect", "mem" *)
lemma image_Collect_mem: "{ f x | x . x \<in> S } = f ` S" by auto

lemma image_union: fixes f X Y shows "f ` (X \<union> Y) = f ` X \<union> f ` Y" by auto

end
