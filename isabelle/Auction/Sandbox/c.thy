(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory c
(*MC@CL: I was thinking about moving everything here into RelationProperties, OK?

CL: Makes sense, almost.  I moved "trivial" to SetUtils, as it is not about _relations_.

Once touching RelationProperties keep in mind that it may contain some code
that is redundant with what you have in a.thy and b.thy.  Such as my old computation of 
injective functions.  Some of this may be obsolete now, or it may be worth preserving in 
an "alternative" section; compare Partitions.
*)
imports
  Real
(*  Equiv_Relations
  "../SetUtils"
  "../RelationProperties"
  "../Partitions"
  "../Maximum"
"$AFP/Collections/common/Misc"*)

begin
  term "semilattice_set.F max"
  
value "quotient {(0::nat,10::nat), (1, 11)} {(0::nat,0)} {(11,11::nat)}"
  
  
value "all_partitions {1::nat}"
value "Max ((%x. 1+1/(real (x::nat)))`({1..<123}))"
value "arg_max' (%x. 1/(real (x::nat))) {1..<123}"

type_synonym ('a,'b)rel = "'a => ('b set)"
abbreviation "Dom (R::(('a,'b)rel)) == R -` (UNIV - {{}})"
abbreviation "Ran (R::(('a,'b)rel)) == \<Union> (range R)"
abbreviation "eval (R::(('a, 'b) rel)) x == the_elem (R x)"
abbreviation "convert r == {(x,y)| x y. x \<in> Dom r & y \<in> r x}"
abbreviation "deconvert R == %x. R``{x}"
abbreviation "Runiq r == ??"
(*
definition kernel where
"kernel R=(op `` (R^-1)) ` (Range (projector (Graph id)))"
-- {* if R is a function, kernel R is the partition of the domain of R
whose each set is made of the elements having the same image through R 
See http://en.wikipedia.org/wiki/Kernel_(set_theory) *} 
(* "kernel R = Range ((Graph id) O Graph ((op ``)(R^-1)))" *)
*)






(* BIGSKIP *)

























(*
lemma l10: fixes X 
(* I assumes "I \<subseteq> (Graph id)" *)
assumes "X \<in> Range (projector (Graph id))" shows "trivial X"
proof - 
let ?Id="Graph id" let ?D="Domain ?Id" let ?XX="{{x}| x .x \<in> ?D}"
have "Range (projector ?Id) = ?XX" using l7 by auto
hence "X \<in> ?XX" using assms by force
then obtain x where 1: "x \<in> ?D & X={x}" by fast
thus "trivial X" using 1 trivial_def by fastforce
qed
*)

(* lemma shows "runiq (projector R O (Graph (%X . (THE x. x\<in>X))))"
using assms projector_def relcomp_def Graph_def runiq_def  *)












































(*
lemma l36: fixes R::"('a \<times> 'b) set"
assumes "(x,y) \<in> part2rel (kernel R)" shows "R``{x} \<inter> (R `` {y}) \<noteq> {}"
using part2rel_def kernel_def Image_def assms 
proof -
let ?I="projector (Graph id)"
have 2: "Range ?I={{x}|x::('b). True}" using l35 by auto
let ?k="(op `` (R^-1)) ` (Range ?I)" let ?E="\<Union> ((% x . (x \<times> x)) ` ?k)"
have "(x,y) \<in> ?E" using assms part2rel_def kernel_def by metis then
obtain X where 0: "(x,y) \<in> (X \<times> X) & X \<in> ?k"
using part2rel_def assms by (smt UnionE imageE)
obtain Z::"'b set" where 1: "X = R^-1 `` Z & Z \<in> Range ?I" using 0 kernel_def Image_def Range_def 
by (smt image_iff)
have "Z \<in> {{x}|x::'b. True}" using 1 2 by auto then
obtain z::'b where 3: "Z={z} & True" by blast
have "x \<in> R^-1 `` {z} & y \<in> R^-1 `` {z}" using 3 0 1 by blast
hence "z \<in> R `` {x} & z \<in> R `` {y}" by fastforce
thus ?thesis by auto
qed
*)



(*
lemma l48: shows "Domain (part2rel (kernel P)) = Domain P" 
proof -
let ?D=Domain let ?k="kernel" let ?p=projector let ?r=part2rel 
let ?f=P let ?XX="?k ?f" let ?Q="?r ?XX" let ?R="?f^-1"
have "?D ?Q= \<Union> ?XX" using l47 by metis
also have "... = ?R `` (\<Union> (Range (?p (Graph id))))" using kernel_def l43 by metis
also have "... = ?R `` (Range (Graph id))" using l46 by metis
also have "... = ?R `` (Domain ?R)" using Graph_def by fastforce
also have "... = Range ?R" by fast
ultimately show "?D ?Q=Domain ?f" by simp
qed
*)


lemma True try


end

