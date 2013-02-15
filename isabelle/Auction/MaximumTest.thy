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

header {* Maximum and related functions *}

theory MaximumTest
imports Maximum
begin

text{* a test vector whose maximum component value we determine *}
value "maximum 2 (\<lambda> x::nat . 1)"
value "maximum 5 (\<lambda> x::nat . x)"

(* for testing *)
lemma test_arg_max_set:
  shows "{1,2} \<subseteq> arg_max_set 3 (\<lambda>x. if x < 3 then 100 else 0)" (* the 1st and 2nd elements in a vector [100,100,\<dots>] are maximal. *)
apply(unfold arg_max_set_def)
apply(simp add: maximum_def)
oops (* TODO CL: This is broken since I've changed "primrec maximum" to "fun maximum" *)

text{* an alternative proof of the same lemma -- still too trivial to test how declarative proofs \emph{actually} work *}
lemma test_arg_max_set_declarative:
  shows "{1,2} \<subseteq> arg_max_set 3 (\<lambda>x. if x < 3 then 100 else 0)" (* the 1st and 2nd elements in a vector [100,100,\<dots>] are maximal. *)
oops (* TODO CL: This is broken since I've changed "primrec maximum" to "fun maximum" *)
(* unfolding arg_max_set_def
  by (simp add: maximum_def) *)

(* for testing *)
value "maximum_except 3 (\<lambda> x::nat . 4-x) 1" (* the maximum component value of the vector [3,2,1], except the first element, is 2 *)

end

