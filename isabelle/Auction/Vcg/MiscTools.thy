(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)


header {* Toolbox of various definitions and theorems about sets, relations and lists *}

theory MiscTools 

imports 
RelationProperties
"~~/src/HOL/Library/Discrete"
Main
RelationOperators
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Indicator_Function"
Argmax

begin

section {* Facts and notations about relations, sets and functions. *}

(* We use as alternative notation for paste instead of +* also +< and overload this with the next definition *)
notation paste (infix "+<" 75)

text {* @{text +<} abbreviation permits to shorten the notation for altering a function f in a single point by giving a pair (a, b) so that the new function has value b with argument a. *}
abbreviation singlepaste where "singlepaste f pair == f +* {(fst pair, snd pair)}"
notation singlepaste (infix "+<" 75) (* Type of g in f +< g should avoid ambiguities *)

text {* @{text "--"} abbreviation permits to shorten the notation for considering a function outside a single point. *}
abbreviation singleoutside (infix "--" 75) where "f -- x \<equiv> f outside {x}"

text {* Turns a HOL function into a set-theoretical function *}
definition (*Graph :: "('a => 'b) => ('a \<times> 'b) set" where *) 
"Graph f = {(x, f x) | x . True}"

text {* Inverts @{term Graph} (which is equivalently done by @{term eval_rel}). *}
(* Assume (x, y) is in R. Apply R to x, i.e., R ,, x,  will result in y assumed y is unique. *)  
definition  "toFunction R = (\<lambda> x . (R ,, x))"

(* toFunction = eval_rel *)
lemma "toFunction = eval_rel" using toFunction_def eval_rel_def by blast

lemma lll40: "((P \<union> Q) || X) = ((P || X) \<union> (Q||X))" unfolding restrict_def using assms by blast

text {* update behaves like P +* Q (paste), but without enlarging P's Domain. update is the set theoretic equivalent of the lambda function update @{term fun_upd} *}
definition update where "update P Q = P +* (Q || (Domain P))"
notation update (infix "+^" 75)

(* The operator runiqer will make out of an arbitrary relation a function by making a choice to all those elements in the domain for which the value is not unique by applying the axiom of choice. *)
definition runiqer  :: "('a \<times> 'b) set => ('a \<times> 'b) set"
where "runiqer R = { (x, THE y. y \<in> R `` {x})| x. x \<in> Domain R }"

text {* @{term graph} is like @{term Graph}, but with a built-in restriction to a given set @{term X}.
This makes it computable for finite X, whereas @{term "Graph f || X"} is not computable. 
Duplicates the eponymous definition found in @{text Function_Order}, which is otherwise not needed. *}
definition graph where "graph X f = {(x, f x) | x. x \<in> X}" 

lemma lm024a: assumes "runiq R" shows "R \<supseteq> graph (Domain R) (toFunction R)" 
unfolding graph_def toFunction_def
using assms graph_def toFunction_def eval_runiq_rel by fastforce

lemma lm024b: assumes "runiq R" shows "R \<subseteq> graph (Domain R) (toFunction R)" 
unfolding graph_def toFunction_def
using assms eval_runiq_rel runiq_basic Domain.DomainI mem_Collect_eq subrelI by fastforce

lemma lm024: assumes "runiq R" shows "R = graph (Domain R) (toFunction R)"
using assms lm024a lm024b by fast

lemma ll37: "runiq(graph X f) & Domain(graph X f)=X" unfolding graph_def using l14 by fast

(* The following definition gives the image of a relation R for a fixed element x. It is equivalent to eval_rel for right unique R, but more general since it determines values even when R is not right unique. *)
abbreviation "eval_rel2 (R::('a \<times> ('b set)) set) (x::'a) == \<Union> (R``{x})"
notation eval_rel2 (infix ",,," 75)

lemma lll82: assumes "runiq (f::(('a \<times> ('b set)) set))" "x \<in> Domain f" shows "f,,x = f,,,x"
using assms Image_runiq_eq_eval cSup_singleton by metis

(* UNIV is the universal set containing everything of the given type. It is defined in Set.thy.*)
lemma ll36: "Graph f=graph UNIV f" unfolding Graph_def graph_def by simp

lemma lm04: "graph (X \<inter> Y) f \<subseteq> ((graph X f) || Y)" unfolding graph_def 
using Int_iff mem_Collect_eq restrict_ext subrelI by auto

definition runiqs where "runiqs={f. runiq f}"

lemma l37a: "((P outside X) outside Y) = P outside (X\<union>Y)" unfolding Outside_def by blast

corollary l37: "((P outside X) outside X) = P outside X" using l37a by force 

lemma l38a: assumes "(X \<inter> Domain P) \<subseteq> Domain Q" shows 
"P +* Q = (P outside X) +* Q" unfolding paste_def Outside_def using assms by blast

corollary l38: "P +* Q = (P outside (Domain Q)) +* Q" using l38a by fast

corollary l39: "R = (R outside {x}) \<union> ({x} \<times> (R `` {x}))" 
using restrict_to_singleton outside_union_restrict by metis

lemma lm72: "P = P \<union> {x}\<times>P``{x}" using assms by (metis l39 sup.right_idem)

corollary l40: "R = (R outside {x}) +* ({x} \<times> (R `` {x}))" 
by (metis paste_outside_restrict restrict_to_singleton)

lemma ll84a: "R \<subseteq> R +* ({x} \<times> (R``{x}))" using 
l40 l38 paste_def Outside_def by fast

lemma ll84b: "R \<supseteq> R+*({x} \<times> (R``{x}))" by (metis 
Un_least Un_upper1 outside_union_restrict paste_def restrict_to_singleton restriction_is_subrel)

lemma ll84: "R = R +* ({x} \<times> (R``{x}))" using ll84a ll84b by force

lemma lll59: assumes "trivial Y" shows "runiq (X \<times> Y)" using assms 
runiq_def Image_subset ll84 trivial_subset ll84a by (metis(no_types))

(* Two constant functions can be combined to a function *)
lemma lm14b: "runiq ((X \<times> {x}) +* (Y \<times> {y}))" using assms lll59 trivial_singleton runiq_paste2 by metis

lemma lll11b: "(P || (X \<inter> Y)) \<subseteq> (P||X)    &    P outside (X \<union> Y) \<subseteq> P outside X" using 
Outside_def restrict_def Sigma_Un_distrib1 Un_upper1 inf_mono Diff_mono 
subset_refl by (metis (lifting) Sigma_mono inf_le1)

lemma lll11: "P || X \<subseteq> (P||(X \<union> Y))       &    P outside X \<subseteq> P outside (X \<inter> Y)" 
using lll11b distrib_sup_le sup_idem 
le_inf_iff subset_antisym sup_commute
by (metis sup_ge1)

lemma lll84: "P``(X \<inter> Domain P) = P``X" by blast

lemma nn57: assumes "card X=1" and "X \<subseteq> Y" shows "Union X \<in> Y" using assms nn56 by (metis cSup_singleton insert_subset)

lemma nn57b: assumes "card X=1" "X \<subseteq> Y" shows "the_elem X \<in> Y" using assms 
by (metis (full_types) insert_subset nn56)

lemma ll52: "(R outside X1) outside X2 = (R outside X2) outside X1" by (metis l37a sup_commute)







section {* ordered relations *}

(* note that card \<^bold>X\<ge>1 means in Isabelle that X is finite and not empty *)
lemma lm79: assumes "card X\<ge>1" "\<forall>x\<in>X. y > x" shows "y > Max X" using assms
by (metis (poly_guards_query) Max_in One_nat_def card_eq_0_iff lessI not_le)

(* assume the function f has a maximum in mx *)
lemma lm80a: assumes "finite X" "mx \<in> X" "f x < f mx" shows"x \<notin> argmax f X" using assms not_less by fastforce

lemma lm80d: assumes "finite X" "mx \<in> X" "\<forall>x \<in> X-{mx}. f x < f mx" shows "argmax f X \<subseteq> {mx}"
using assms mk_disjoint_insert by force

lemma lm80: assumes "finite X" "mx \<in> X" "\<forall>x \<in> X-{mx}. f x < f mx" shows "argmax f X = {mx}" 
using assms lm80d by (metis argmax_non_empty_iff equals0D subset_singletonD)

(* The following corollary is essentially the same as lm80, however, is simplifies a proof in UniformTieBreaking.thy *)
corollary lm80c: "(finite X & mx \<in> X & (\<forall>aa \<in> X-{mx}. f aa < f mx)) \<longrightarrow> argmax f X = {mx}"
using assms lm80 by metis

corollary lm80b: assumes "finite X" "mx \<in> X" "\<forall>x \<in> X. x \<noteq> mx \<longrightarrow> f x < f mx" shows "argmax f X = {mx}"
using assms lm80 by (metis Diff_iff insertI1)

lemma lm75f: assumes "f \<circ> g = id" shows "inj_on g UNIV" using assms 
by (metis inj_on_id inj_on_imageI2)

(* Note that Pow X is the powerset of X *)
lemma lm74a: assumes "inj_on f X" shows "inj_on (image f) (Pow X)"
using assms inj_on_image_eq_iff inj_onI PowD by (metis (mono_tags, lifting))

lemma lm74: assumes "inj_on f Y" "X \<subseteq> Y" shows "inj_on (image f) (Pow X)"
using assms lm74a by (metis subset_inj_on)

(* the finest possible partition of X, e.g., X = {1, 2, 3} goes to {{1}, {2}, {3}}. *)
definition finestpart where "finestpart X = (%x. {x}) ` X"

lemma ll64: "finestpart X = {{x}|x . x\<in>X}" unfolding finestpart_def by blast

lemma lm75: "X=\<Union> (finestpart X)" using ll64 by auto

lemma lm75b: "Union \<circ> finestpart = id" using finestpart_def lm75 by fastforce

lemma lm75c: "inj_on Union (finestpart ` UNIV)" using assms lm75b by (metis inj_on_id inj_on_imageI)

lemma lm31: assumes "X \<noteq> Y" shows "{{x}| x. x \<in> X} \<noteq> {{x}| x. x \<in> Y}" using assms by auto

corollary lm31b: "inj_on finestpart UNIV" using lm31 ll64 by (metis (lifting, no_types) injI)

(* E.g. in the following example, with X = {{1}, {1,2}}, x can be {1} and {1,2} and Y is {{1}} and {{1},{2}}, that is, the lefthand and righthand sides evaluate to {{1},{2}} *)
lemma lm55m: "{Y | Y. EX x.((Y \<in> finestpart x) & (x \<in> X))} = \<Union>(finestpart`X)" by auto

(* Now we specialize the previous lemma to the situation where X consists of a relation (that is is a set of pairs) *)
lemma lm55l: "Range {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> X} = 
{Y. EX x. ((Y \<in> finestpart x) & (x \<in> Range X))}" by auto

(* Further specialization to a singleton for Y *)
lemma lm55j: "{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> X} = 
{(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> X}"
using finestpart_def by fastforce

lemma lm55b: "{(fst pair, {y})| y. y \<in>  snd pair} = {fst pair} \<times> {{y}| y. y \<in> snd pair}" by fastforce

lemma lm71: "x \<in> X = ({x} \<in> finestpart X)" using finestpart_def by force

lemma nn43: "{(x,X)}-{(x,Y)} = {x}\<times>({X}-{Y})" by blast

lemma nn11: assumes "\<Union> P = X" shows "P \<subseteq> Pow X" using assms by blast

lemma lm85: "argmax f {x} = {x}" using argmax_def by auto

lemma lm64: assumes "finite X" shows "set (sorted_list_of_set X) = X" using assms by simp

(* We assume for the next lemma that f has value in numbers, and setsum f A is
   sum f(x) for x in A. *)
lemma lll23: assumes "finite A" shows "setsum f A = setsum f (A \<inter> B) + setsum f (A - B)" using 
assms by (metis DiffD2 Int_iff Un_Diff_Int Un_commute finite_Un setsum.union_inter_neutral)

lemma ll56a: assumes "(Domain P \<subseteq> Domain Q)" shows "(P +* Q) = Q"
unfolding paste_def Outside_def using assms by fast

lemma ll56b: assumes "(P +* Q=Q)" shows "(Domain P \<subseteq> Domain Q)"
using assms paste_def Outside_def by blast

lemma ll56: "(Domain P \<subseteq> Domain Q) = (P +* Q=Q)" using ll56a ll56b by metis

lemma "(P||(Domain Q)) +* Q = Q" by (metis Int_lower2 ll41 ll56)

lemma lll00: "P||X   =   P outside (Domain P - X)" 
using Outside_def restrict_def by fastforce

lemma lll01b: "(P outside X) \<subseteq>    P || ((Domain P)-X)" 
using lll00 lll11 by (metis Int_commute ll41 outside_reduces_domain)

lemma lll06a: shows "Domain (P outside X) \<inter> Domain (Q || X) = {}" using lll00 by 
(metis Diff_disjoint Domain_empty_iff Int_Diff inf_commute ll41 outside_reduces_domain restrict_empty)

lemma lll06b: shows "(P outside X) \<inter> (Q || X) = {}" using lll06a by fast

lemma lll06c: shows "(P outside (X \<union> Y)) \<inter> (Q || X) = {} & 
(P outside X) \<inter> (Q || (X \<inter> Z)) = {}
" using assms Outside_def restrict_def lll06b lll11b by fast

lemma lll01: shows "P outside X    =    P || ((Domain P) - X)" 
using Outside_def restrict_def  lll01b by fast

lemma lll99: "R``(X-Y) = (R||X)``(X-Y)" using restrict_def by blast

(* x is a (non-empty) element of the family XX whose union is a subset of X *)
lemma lll79: assumes "\<Union> XX \<subseteq> X" "x \<in> XX" "x \<noteq> {}" shows "x \<inter> X \<noteq> {}" using assms by blast

(* Note that set converts lists such as L1 into sets. L1 is here a list of lists and l an element, that is, a list. We assume furthermore that f2 is constant function with the fixed 2nd argument N. Then we can convert lists to sets in a canonical way. *)
lemma lm66: assumes "\<forall>l \<in> set L1. set L2 = f2 (set l) N" shows 
"set [set L2. l <- L1]  =  {f2 P N| P. P \<in> set (map set L1)}" using assms by auto

(* Variant of the previous lemma *)
lemma lm66b: "(\<forall>l \<in> set (g1 G). set (g2 l N) = f2 (set l) N) --> 
{f2 P N| P. P \<in> set (map set (g1 G))} = set [set (g2 l N). l <- g1 G]" by auto

lemma lll86: assumes "X \<inter> Y  =  {}" shows "R``X = (R outside Y)``X"
using assms Outside_def Image_def by blast

(* lemma lm02: "argmax f A = { x \<in> A . f x = Max (f ` A) }" using assms by simp
*)





(* *** *)














































abbreviation "mylog n == (if (n \<noteq> 0) then (Discrete.log n) else (-1))"
abbreviation "Card X == mylog (card (Pow X))"
lemma assumes "finite X" shows "Card X = card X" (is "?L=?R") using assms 
proof -
have "Card X=Discrete.log (card (Pow X))" using assms by auto
moreover have "... = Discrete.log (2^card X)" using assms by (metis (poly_guards_query) card_Pow)
ultimately show ?thesis by fastforce
qed

lemma assumes "\<not> (finite X)" shows "Card X=-1" using assms by simp

lemma lll77: assumes "Range P \<inter> (Range Q)={}" "runiq (P^-1)" "runiq (Q^-1)" shows "runiq ((P \<union> Q)^-1)"
using assms by (metis Domain_converse converse_Un disj_Un_runiq)

lemma lll77b: assumes "Range P \<inter> (Range Q)={}" "runiq (P^-1)" "runiq (Q^-1)" 
shows "runiq ((P +* Q)^-1)"
using lll77 assms subrel_runiq by (metis converse_converse converse_subset_swap paste_sub_Un)

lemma l32: "runiq R = (\<forall> x . trivial (R``{x}))"
using assms by (metis runiq_alt) (* MC TODO: redundant duplicate of runiq_alt *)


lemma lm014: assumes "runiq R" shows "card (R `` {a}) = 1 \<longleftrightarrow> a \<in> Domain R"
using assms card_Suc_eq One_nat_def  by (metis Image_within_domain' Suc_neq_Zero assms lm013)

lemma "inj_on  (%a. ((fst a, fst (snd a)), snd (snd a))) UNIV" 
by (metis (lifting, mono_tags) Pair_fst_snd_eq Pair_inject injI)
lemma nn27: assumes "finite X" "x > Max X" shows "x \<notin> X" using assms Max.coboundedI by (metis leD)

lemma lm86: assumes "finite A" "A \<noteq> {}" shows "Max (f`A) \<in> f`A" 
using assms by (metis Max_in finite_imageI image_is_empty)

lemma "argmax f A \<subseteq> f -` {Max (f ` A)}" by force

lemma lm78: "argmax f A = A \<inter>{ x . f x = Max (f ` A) }" by auto

lemma nn60: "(x \<in> argmax f X) = (x \<in> X & f x = Max {f xx| xx. xx \<in> X})" 
using argmax.simps image_Collect_mem mem_Collect_eq
by (metis (mono_tags, lifting))

corollary nn59: assumes "finite g" shows "setsum f g = setsum f (g outside X) + (setsum f (g||X))" 
unfolding Outside_def restrict_def using assms add.commute inf_commute lll23 by (metis)

lemma lm51: "Range -` {{}} = {{}}" by auto

lemma lm47: "(\<forall> pair \<in> a. finite (snd pair)) = (\<forall> y \<in> Range a. finite y)" by fastforce

lemma lm38e: "fst ` P = snd ` (P^-1)" by force
lemma lm38d: "fst z =snd (flip z) & snd z=fst (flip z)" unfolding flip_def by simp
lemma flip_flip2: "flip \<circ> flip=id" using flip_flip by fastforce
lemma lm38f: "fst=(snd\<circ>flip)" using lm38d by fastforce
lemma lm38g: "snd=(fst\<circ>flip)" using lm38d by fastforce
lemma lm38h: "inj_on fst P = inj_on (snd\<circ>flip) P" using lm38f by metis
lemma lm38c: "inj_on fst P = inj_on snd (P^-1)" 
using lm38h flip_conv by (metis converse_converse inj_on_imageI lm38g)

lemma lm39: assumes "runiq (a^-1)" shows "setsum (card \<circ> snd) a = setsum card (Range a)" 
using assms lm38c converse_converse lll31 setsum.reindex snd_eq_Range by metis

lemma lm29: assumes "X \<noteq> {}" shows "finestpart X \<noteq> {}" using assms finestpart_def by blast

lemma assumes "inj_on g X" shows "setsum f (g`X) = setsum (f \<circ> g) X" using assms by (metis setsum.reindex)

lemma lm60: assumes "runiq R" "z \<in> R" shows "R,,(fst z) = snd z" 
using assms by (metis l31 surjective_pairing)

lemma lm59: assumes "runiq R" shows "setsum (toFunction R) (Domain R) = setsum snd R" using 
assms toFunction_def setsum.reindex_cong lm60 lll31 by (metis (no_types) fst_eq_Domain)

corollary lm59b: assumes "runiq (f||X)" shows "setsum (toFunction (f||X)) (X \<inter> Domain f) =
setsum snd (f||X)" using assms lm59 by (metis Int_commute ll41)

lemma lll85b: "Range (R outside X) = R``(Domain R - X)" 
using assms by (metis Diff_idemp ImageE Range.intros Range_outside_sub_Image_Domain lll01 lll99 order_class.order.antisym subsetI)

lemma "(R||X) `` X = R``X" using Int_absorb lll02 lll85 by metis
lemma lm61: assumes "x \<in> Domain (f||X)" shows "(f||X)``{x} = f``{x}" using assms
lll02 lll85 Int_empty_right Int_iff Int_insert_right_if1 ll41 by metis
lemma lm61b: assumes "x \<in> X \<inter> Domain f" "runiq (f||X)" shows "(f||X),,x = f,,x" 
using assms lll02 lll85 Int_empty_right Int_iff Int_insert_right_if1 eval_rel.simps by metis

lemma lm61c: assumes "runiq (f||X)" shows 
"setsum (toFunction (f||X)) (X \<inter> Domain f) = setsum (toFunction f) (X \<inter> Domain f)" 
using assms setsum.cong lm61b toFunction_def by metis
corollary lm59c: assumes "runiq (f||X)" shows 
"setsum (toFunction f) (X \<inter> Domain f) = setsum snd (f||X)" using assms lm59b lm61c by fastforce

corollary assumes "runiq (f||X)" shows "setsum (toFunction (f||X)) (X \<inter> Domain f) = setsum snd (f||X)" 
using assms lm59 ll41 Int_commute by metis
lemma lm26: "card (finestpart X) = card X" 
using finestpart_def by (metis (lifting) card_image inj_on_inverseI the_elem_eq)
corollary lm26b: "finestpart {} = {} & card \<circ> finestpart = card" using lm26 finestpart_def by fastforce

lemma lm40: "finite (finestpart X) = finite X" using assms finestpart_def lm26b 
by (metis card_eq_0_iff empty_is_image finite.simps lm26)
lemma "finite \<circ> finestpart = finite" using lm40 by fastforce

lemma lll34: assumes "runiq P" shows "card (Domain P) = card P" 
using assms lll33 card_image by (metis Domain_fst)

lemma lm43: assumes "runiq f" shows "finite (Domain f) = finite f" 
using assms Domain_empty_iff card_eq_0_iff finite.emptyI lll34 by metis

lemma lm24: "setsum ((curry f) x) Y = setsum f ({x} \<times> Y)"
proof -
let ?f="% y. (x, y)" let ?g="(curry f) x" let ?h=f
have "inj_on ?f Y" by (metis(no_types) Pair_inject inj_onI) 
moreover have "{x} \<times> Y = ?f ` Y" by fast
moreover have "\<forall> y. y \<in> Y \<longrightarrow> ?g y = ?h (?f y)" by simp
ultimately show ?thesis using setsum.reindex_cong by metis
qed

lemma lm24b: "setsum (%y. f (x,y)) Y = setsum f ({x}\<times>Y)" 
using lm24 Sigma_cong curry_def setsum.cong by fastforce

corollary lm12: assumes "finite X" shows "setsum f X = setsum f (X-Y) + (setsum f (X \<inter> Y))" 
using assms Diff_iff IntD2 Un_Diff_Int finite_Un inf_commute setsum.union_inter_neutral by metis

lemma ll50: "(P +* Q)``(Domain Q\<inter>X)=Q``(Domain Q\<inter>X)" 
unfolding paste_def Outside_def Image_def Domain_def by blast

corollary "(P +* Q)``(X\<inter>(Domain Q))=Q``X" using Int_commute ll50 by (metis lll84)

corollary lm19: assumes "X \<inter> Domain Q = {}" (is "X \<inter> ?dq={}") shows "(P +* Q) `` X = (P outside ?dq)`` X" 
using assms paste_def by fast

lemma lm20: assumes "X\<inter>Y={}" shows "(P outside Y)``X=P``X" using assms Outside_def by blast

corollary lm19b: assumes "X\<inter>Domain Q={}" shows "(P +* Q)``X=P``X" using assms lm19 lm20 by metis

lemma lm23: assumes "finite X" "finite Y" "card(X\<inter>Y)=card X" shows "X\<subseteq>Y" using assms 
by (metis Int_lower1 Int_lower2 card_seteq order_refl)

lemma lm23b: assumes "finite X" "finite Y" "card X =card Y" shows "(card (X\<inter>Y)=card X)=(X=Y)"
using assms lm23 by (metis card_seteq le_iff_inf order_refl)

lemma l16: (*fixes f::"'a => 'b" fixes P::"'a => bool" fixes xx::"'a"*) assumes "P xx" shows 
"{(x,f x)| x. P x},,xx=f xx" (*MC: as a corollary of ll88?*)
proof -
let ?F="{(x,f x)| x. P x}" let ?X="?F``{xx}"
have "?X={f xx}" using Image_def assms by blast thus ?thesis by fastforce 
qed

lemma ll33: assumes "x \<in> X" shows "graph X f,,x=f x" 
unfolding graph_def using assms l16 by (metis (mono_tags) Gr_def)

lemma ll28: "Graph f,,x=f x" using UNIV_I ll33 ll36 by (metis(no_types))

lemma "toFunction (Graph f)=f" (is "?L=_") 
proof-{fix x have "?L x=f x" unfolding toFunction_def ll28 by metis}thus ?thesis by blast qed

lemma nn29: "R outside X \<subseteq> R" by (metis outside_union_restrict subset_Un_eq sup_left_idem)

lemma nn30a: "Range(f outside X) \<supseteq> (Range f)-(f``X)" using assms Outside_def by blast

lemma lll71b: assumes "runiq P" shows "P\<inverse>``((Range P)-X)\<inter>((P\<inverse>)``X)={}"
using assms ll71 by blast

lemma lll78: assumes "runiq (P\<inverse>)" shows "P``(Domain P - X)\<inter>(P``X)={}"
using assms ll71 by fast

lemma nn30b: assumes "runiq f" "runiq (f^-1)" shows "Range(f outside X)\<subseteq>(Range f)-(f``X)" 
using assms Diff_triv lll78 lll85b Diff_iff ImageE Range_iff subsetI by metis 
lemma nn30: assumes "runiq f" "runiq (f^-1)" shows "Range(f outside X)=(Range f)-(f``X)" 
using assms nn30a nn30b by (metis order_class.order.antisym)

lemma lm42: "(\<forall>x\<in>X. \<forall>y\<in>Y. x\<inter>y={})=(\<Union>X\<inter>(\<Union> Y)={})" by blast

lemma "Domain ((a outside (X \<union> {i})) \<union> ({(i, \<Union> (a``(X \<union> {i})))} - {(i,{})}) ) 
\<subseteq> Domain a - X \<union> {i}" using assms Outside_def by auto

lemma "(R - ((X\<union>{i})\<times>(Range R))) = (R outside X) outside {i}" using Outside_def 
by (metis l37a)

lemma "{(i, x)} - {(i,y)} = {i} \<times> ({x}-{y})" by fast

lemma lm44: "{x}-{y}={} = (x=y)" by auto

lemma assumes "R \<noteq> {}" "Domain R \<inter> X \<noteq> {}" shows "R``X \<noteq> {}" using assms by blast

lemma "R``{}={}" by (metis Image_empty)

lemma lm56: "R \<subseteq> (Domain R) \<times> (Range R)" by auto

lemma lm57: "(finite (Domain Q) & finite (Range Q)) = finite Q" using 
rev_finite_subset finite_SigmaI lm56 finite_Domain finite_Range by metis

lemma lll41: assumes "finite (\<Union> XX)" shows "\<forall>X \<in> XX. finite X" using assms
by (metis Union_upper finite_subset)

lemma ll57: (*repetition*) fixes a::real fixes b c shows "a*b - a*c=a*(b-c)"
using assms by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

lemma lll62: fixes a::real fixes b c shows "a*b - c*b=(a-c)*b" (*MC: repetition*)
using assms ll57 by (metis comm_semiring_1_class.normalizing_semiring_rules(7))

lemma ll71b: assumes "runiq f" "X \<subseteq> (f^-1)``Y" shows "f``X \<subseteq> Y" using assms ll71 by (metis Image_mono order_refl subset_trans)

lemma l31b: assumes "y \<in> f``{x}" "runiq f" shows "f,,x = y" using assms
by (metis Image_singleton_iff l31)















section {* Indicator function in set-theoretical form. *}

abbreviation "Outside' X f == f outside X"
abbreviation "Chi X Y == (Y \<times> {0::nat}) +* (X \<times> {1})"
notation Chi (infix "<||" 80)
abbreviation "chii X Y == toFunction (X <|| Y)"
notation chii (infix "<|" 80)
abbreviation "chi X == indicator X"

lemma lm13: "runiq (X <|| Y)" by (metis lll59 runiq_paste2 trivial_singleton)

lemma lm14c: assumes "x \<in> X" shows "1 \<in> (X <|| Y) `` {x}" using assms toFunction_def 
paste_def Outside_def runiq_def lm14b by blast

lemma lm14d: assumes "x \<in> Y-X" shows "0 \<in> (X <|| Y) `` {x}" using assms toFunction_def
paste_def Outside_def runiq_def lm14b by blast

lemma lm14e: assumes "x \<in> X \<union> Y" shows "(X <|| Y),,x = chi X x" (is "?L=?R") using 
assms lm14b lm14c lm14d l31b by (metis DiffI Un_iff indicator_simps(1) indicator_simps(2))

lemma lm14f: assumes "x \<in> X \<union> Y" shows "(X <| Y) x = chi X x" (is "?L=?R") 
using assms toFunction_def lm14e by metis
corollary lm15b: "setsum (X <| Y) (X\<union>Y) = setsum (chi X) (X\<union>Y)"
using lm14f setsum.cong by metis

corollary lmm02: assumes "!x:X. f x = g x" shows "setsum f X = setsum g X" using assms 
by (metis (poly_guards_query) setsum.cong)
corollary lm02b: assumes "!x:X. f x = g x" "Y\<subseteq>X" shows "setsum f Y = setsum g Y" using assms lmm02
by (metis contra_subsetD)

corollary lm15: assumes "Z \<subseteq> X \<union> Y" shows "setsum (X <| Y) Z = setsum (chi X) Z"  
proof - 
have "!x:Z.(X<|Y) x=(chi X) x" using assms lm14f in_mono by metis thus ?thesis using lmm02 by blast 
qed

corollary lm16: "setsum (chi X) (Z - X) = 0" by simp

corollary lm17: assumes "Z \<subseteq> X \<union> Y" shows "setsum (X <| Y) (Z - X) = 0" 
using assms lm16 lm15 Diff_iff in_mono subsetI by metis

corollary lm18: assumes "finite Z" shows "setsum (X <| Y) Z = setsum (X <| Y) (Z - X) 
+(setsum (X <| Y) (Z \<inter> X))" using lm12 assms by blast

corollary lm18b: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "setsum (X <| Y) Z = setsum (X <| Y) (Z \<inter> X)" 
using assms lm12 lm17 comm_monoid_add_class.add.left_neutral by metis

corollary lm21: assumes "finite Z" shows "setsum (chi X) Z = card (X \<inter> Z)" using assms 
setsum_indicator_eq_card by (metis Int_commute)

corollary lm22: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "setsum (X <| Y) Z = card (Z \<inter> X)"
using assms lm21 by (metis lm15 setsum_indicator_eq_card)

corollary lm28: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "(setsum (X <| Y) X) - (setsum (X <| Y) Z) =
card X - card (Z \<inter> X)" using assms lm22 by (metis Int_absorb2 Un_upper1 card_infinite equalityE setsum.infinite)

corollary lm28b: assumes "Z \<subseteq> X \<union> Y" "finite Z" shows "int (setsum (X <| Y) X) - int (setsum (X <| Y) Z) =
int (card X) - int (card (Z \<inter> X))" using assms lm22 by (metis Int_absorb2 Un_upper1 card_infinite equalityE setsum.infinite)

lemma lm28c: "int (n::nat) = real n" by simp

corollary lm28d: assumes "Z\<subseteq>X\<union>Y" "finite Z" shows 
"real (setsum (X <| Y) X) - real (setsum (X <| Y) Z) = real (card X) - real (card (Z \<inter> X))" 
using assms lm22 by (metis Int_absorb2 Un_upper1 card_infinite equalityE setsum.infinite)



































lemma lm84c: assumes "\<exists> n \<in> {0..<size l}. P (l!n)" shows "[n. n \<leftarrow> [0..<size l], P (l!n)] \<noteq> []"
using assms by auto
lemma lm84d: assumes "ll \<in> set (l::'a list)" shows "\<exists> n\<in> (nth l) -` (set l). ll=l!n"
using assms(1) by (metis in_set_conv_nth vimageI2)
lemma lm84e: assumes "ll \<in> set (l::'a list)" shows "\<exists> n. ll=l!n & n < size l & n >= 0"
using assms in_set_conv_nth by (metis le0)
lemma "(nth l) -` (set l) \<supseteq> {0..<size l}" using assms by fastforce
lemma lm84f: assumes "P -` {True} \<inter> set l \<noteq> {}" shows "\<exists> n \<in> {0..<size l}. P (l!n)" 
using assms lm84e by fastforce

lemma lm84g: assumes "P -` {True} \<inter> set l \<noteq> {}" shows "[n. n \<leftarrow> [0..<size l], P (l!n)] \<noteq> []" 
using assms filterpositions2_def lm84f lm84c by metis

lemma nn06: "(nth l) ` set ([n. n \<leftarrow> [0..<size l], (%x. x\<in>X) (l!n)]) \<subseteq> X\<inter>set l" by force
corollary nn06b: "(nth l)` set (filterpositions2 (%x.(x\<in>X)) l) \<subseteq> X \<inter>  set l" 
unfolding filterpositions2_def using nn06 by fast

lemma "(n\<in>{0..<N}) = ((n::nat) < N)" using atLeast0LessThan lessThan_iff by metis
lemma nn01: assumes "X \<subseteq> {0..<size list}" shows "(nth list)`X \<subseteq> set list" 
using assms atLeastLessThan_def atLeast0LessThan lessThan_iff by auto
lemma lm99: "set ([n. n \<leftarrow> [0..<size l], P (l!n)]) \<subseteq> {0..<size l}" by force
lemma lm99b: "set (filterpositions2 pre list) \<subseteq> {0..<size list}" using filterpositions2_def lm99 by metis

lemma lm55n: assumes "X \<subseteq> Y" shows "finestpart X \<subseteq> finestpart Y" using assms finestpart_def by (metis image_mono)
corollary lm55o: assumes "x \<in> X" shows "finestpart x \<subseteq> finestpart (\<Union> X)" using assms
lm55n by (metis Union_upper)
lemma lm55p: "\<Union> (finestpart ` XX) \<subseteq> finestpart (\<Union> XX)" using assms finestpart_def 
lm55o by force
lemma lm55q: "\<Union> (finestpart ` XX) \<supseteq> finestpart (\<Union> XX)" (is "?L \<supseteq> ?R") 
unfolding finestpart_def using finestpart_def by auto

corollary lm55r: "\<Union> (finestpart ` XX) = finestpart (\<Union> XX)" using lm55p lm55q by fast

lemma lm55h: assumes "runiq a" shows "{(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a} = 
{(x, {y})| x y. y \<in> a,,x & x \<in> Domain a}" using assms Image_runiq_eq_eval 
by (metis (lifting, no_types) cSup_singleton)

subsection {* Computing all the permutations of a list *}
abbreviation "rotateLeft == rotate"
abbreviation "rotateRight n l == rotateLeft (size l - (n mod (size l))) l"
abbreviation "insertAt x l n == rotateRight n (x#(rotateLeft n l))"
(* for n in {0, ..., size l} inserts x in l so that it will have index n in the output*)
(* note that for other n, the behaviour is not guaranteed to be consistent with that *)
fun perm2 where
"perm2 [] = (%n. [])" | 
"perm2 (x#l) = (%n. insertAt x ((perm2 l) (n div (1+size l))) (n mod (1+size l)))"
(* for n in {0,..., fact(size l) - 1 }, 
perm2 l n gives all and only the possible permutations of l *)
abbreviation "takeAll pre list == map (nth list) (filterpositions2 pre list)"

lemma lm83: assumes "l \<noteq> []" shows "perm2 l n \<noteq> []" 
using assms perm2_def perm2.simps(2) rotate_is_Nil_conv by (metis neq_Nil_conv)
lemma lm98: "set (takeAll pre list) = ((nth list) ` set (filterpositions2 pre list))" by simp

corollary nn06c: "set (takeAll (%x.(x\<in>X)) l) \<subseteq> X\<inter>set l" using nn06b lm98 by metis

corollary nn02: "set (takeAll pre list) \<subseteq> set list" using lm99b lm98 nn01 by metis
lemma nn03: "set (insertAt x l n) = {x} \<union> set l" by simp
lemma nn04a: "\<forall>n. set (perm2 [] n) = set []" by simp
lemma nn04b: assumes "\<forall>n. (set (perm2 l n) = set l)" shows "set (perm2 (x#l) n) = {x} \<union> set l" 
using assms perm2_def nn03 by force
corollary nn04: "\<forall>n. set (perm2 l n) = set l" 
(* MC: this is weaker than saying (perm2 l n) is a permutation of l *) 
proof (induct l)
let ?P="%l. (\<forall>n. set (perm2 l n)=set l)"
show "?P []" using nn04a by force next let ?P="%l. (\<forall>n. set (perm2 l n)=set l)"
fix x fix l assume "?P l" then show "?P (x#l)" by force
qed

corollary nn05a: "set (perm2 (takeAll (%x.(x\<in>X)) l) n) \<subseteq> X \<inter> set l" using nn06c nn04 by metis


section {* A more computable version of @{term toFunction}.*}

abbreviation "toFunctionWithFallback R fallback == (% x. if (R``{x}={R,,x}) then (R,,x) else fallback)"
notation toFunctionWithFallback (infix "Else" 75)
abbreviation "setsum' R X == setsum (R Else 0) X"
abbreviation "setsum'' R X == setsum (toFunction R) (X \<inter> Domain R)"
abbreviation "setsum''' R X == setsum' R (X\<inter>Domain R)"
abbreviation "setsum'''' R X == setsum (%x. setsum id (R``{x})) X"

lemma nn47: assumes "runiq f" "x \<in> Domain f" shows "(f Else 0) x = (toFunction f) x" using assms 
by (metis Image_runiq_eq_eval toFunction_def)

lemma nn48b: assumes "runiq f" shows "setsum (f Else 0) (X\<inter>(Domain f)) = setsum (toFunction f) (X\<inter>(Domain f))" 
using assms setsum.cong nn47 by fastforce
lemma nn51: assumes "Y \<subseteq> f-`{0}" shows "setsum f Y=0" using assms 
by (metis set_rev_mp setsum.neutral vimage_singleton_eq)

lemma nn49: assumes "Y \<subseteq> f-`{0}" "finite X" shows "setsum f X = setsum f (X-Y)" 
using assms Int_lower2 comm_monoid_add_class.add.right_neutral inf.boundedE inf.orderE lm12 nn51
by (metis(no_types))

lemma nn50: "-(Domain f) \<subseteq> (f Else 0)-`{0}" by fastforce

corollary nn52: assumes "finite X" shows "setsum (f Else 0) X=setsum (f Else 0) (X\<inter>Domain f)" 
proof- have "X\<inter>Domain f=X-(-Domain f)" by simp thus ?thesis using assms nn50 nn49 by fastforce qed
corollary nn52b: assumes "finite X" shows "setsum (f Else 0) (X\<inter>Domain f)=setsum (f Else 0) X"
(is "?L=?R") proof - have "?R=?L" using assms by (rule nn52) thus ?thesis by simp qed

corollary nn48c: assumes "finite X" "runiq f" shows 
"setsum (f Else 0) X = setsum (toFunction f) (X\<inter>Domain f)" (is "?L=?R") 
proof -
have "?R = setsum (f Else 0) (X\<inter>Domain f) " using assms(2) nn48b by fastforce
moreover have "... = ?L" using assms(1) by (rule nn52b) ultimately show ?thesis by presburger
qed

lemma nn53: "setsum (f Else 0) X = setsum' f X" by fast

corollary nn48d: assumes "finite X" "runiq f" shows "setsum (toFunction f) (X\<inter>Domain f) = setsum' f X"
using assms nn53 nn48c by fastforce
lemma "argmax (setsum' b) = (argmax \<circ> setsum') b" by simp

lemma lm015: assumes "runiq R" "runiq (R^-1)" shows "R``A \<inter> (R``B) = R``(A\<inter>B)" 
using assms lll33 converse_Image by force

lemma lm41: assumes "runiq (R^-1)" "runiq R" "X1 \<inter> X2 = {}" shows "R``X1 \<inter> (R``X2) = {}"
using assms by (metis disj_Domain_imp_disj_Image inf_assoc inf_bot_right)

lemma ll70: assumes "runiq f" "trivial Y" shows "trivial (f `` (f^-1 `` Y))"
using assms by (metis ll71 trivial_subset)

lemma lm020: assumes "trivial X" shows "card (Pow X)\<in>{1,2}" using lm007 card_Pow 
Pow_empty assms lm54 nn56 power_one_right the_elem_eq by (metis insert_iff)

lemma lm017: assumes "card (Pow A)=1" shows "A={}" using assms 
by (metis Pow_bottom Pow_top nn56 singletonD)

lemma lm022: "(\<not> (finite A)) = (card (Pow A) = 0)" by auto

corollary lm022b: "(finite A) = (card (Pow A) \<noteq> 0)" using lm022 by metis

lemma lm016: assumes "card (Pow A) \<noteq> 0" shows "card A=Discrete.log (card (Pow A))" using assms 
log_exp card_Pow by (metis card_infinite finite_Pow_iff)

lemma lm018: assumes "card (Pow A)=2" shows "card A=1" using assms lm016 
by (metis(no_types) comm_semiring_1_class.normalizing_semiring_rules(33) log_exp zero_neq_numeral)

lemma lm019: assumes "card (Pow X)=1 \<or> card (Pow X)=2" shows "trivial X" 
using assms lm007 lm017 lm018 nn56 by metis

lemma lm021: "trivial A = (card (Pow A) \<in> {1,2})" using lm019 lm020 by blast

lemma assumes "R\<subseteq>f" "runiq f" "Domain f = Domain R" shows "runiq R"
using assms by (metis subrel_runiq)

lemma ll81a: assumes "f \<subseteq> g" "runiq g" "Domain f = Domain g" shows "g \<subseteq> f"
using assms Domain_iff contra_subsetD runiq_wrt_ex1 subrelI
by (metis (full_types,hide_lams))

lemma ll81: assumes "R\<subseteq>f" "runiq f" "Domain f \<subseteq> Domain R" shows "f=R" 
using assms ll81a by (metis Domain_mono dual_order.antisym)

lemma lm06: "graph X f = Graph f || X" using inf_top.left_neutral ll36 ll37 ll41 
ll81 lm04 restriction_is_subrel subrel_runiq subset_iff by (metis (erased, lifting))
lemma lm05: "graph (X \<inter> Y) f = graph X f || Y" using lll02 lm06 by metis
lemma lm65:"{(x, f x)| x. x \<in> X2} || X1 = {(x, f x)| x. x \<in> X2 \<inter> X1}" using graph_def lm05 by metis

lemma lm10: assumes "runiq f" "X \<subseteq> Domain f" shows "graph X (toFunction f) = (f||X)" 
proof -
  have "\<And>v w. (v\<Colon>'a set) \<subseteq> w \<longrightarrow> w \<inter> v = v" by (simp add: Int_commute inf.absorb1)
  thus "graph X (toFunction f) = f || X" by (metis assms(1) assms(2) lll02 lm024 lm06)
qed

lemma l4: "(Graph f) `` X = f ` X" unfolding Graph_def image_def by auto

lemma lm025: assumes "X \<subseteq> Domain f" "runiq f" shows "f``X = (eval_rel f)`X"
using assms l4 by (metis lll85 lm06 lm10 toFunction_def)

lemma lm011: assumes "card A=1" shows "card (f`A)=1" using assms card_image card_image_le 
proof -
have "finite (f`A)" using assms One_nat_def Suc_not_Zero card_infinite finite_imageI by (metis(no_types)) 
moreover have "f`A \<noteq> {}" using assms by fastforce
moreover have "card (f`A) \<le> 1" using assms card_image_le One_nat_def Suc_not_Zero card_infinite by (metis)
ultimately show ?thesis by (metis assms image_empty image_insert nn56 the_elem_eq)
qed

lemma lm012: assumes "card A=1" shows "the_elem (f`A) = f (the_elem A)"using assms 
image_empty image_insert the_elem_eq by (metis nn56)

abbreviation "swap f == curry ((split f) \<circ> flip)" (*swaps the two arguments of a function*)

lemma lm45: "finite X=(X \<in> range set)" by (metis List.finite_set finite_list image_iff rangeI)

lemma lm45b: "finite=(%X. X\<in>range set)" using lm45 by metis

lemma lm46: "swap f = (%x. %y. f y x)" by (metis comp_eq_dest_lhs curry_def flip_def fst_conv old.prod.case snd_conv)
(* lemma "swap = curry \<circ> (((swap (op \<circ>)) flip) \<circ> split)" using lm29 sledgehammer[provers=z3] *)
lemma "finite=(swap (op \<in>))(range set)" unfolding lm46 using lm45b by blast

end

