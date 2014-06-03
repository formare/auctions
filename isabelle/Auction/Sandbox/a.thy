theory a

imports Main Random Random_Sequence
"../Maximum"
"../CombinatorialVickreyAuction"
"~~/src/HOL/Library/Code_Target_Nat"
(* "~~/src/HOL/Library/DAList" *)

begin

lemma "arg_max' f A \<subseteq> f -` {Max (f ` A)}"
using assms arg_max'_def Max_def image_def 
vimage_def 
by force

lemma m00: "arg_max' f A = A \<inter>{ x . f x = Max (f ` A) }"
using assms arg_max'_def Max_def image_def vimage_def
by auto

lemma "arg_max' f A = A \<inter> f -` {Max (f ` A)}"
using assms arg_max'_def Max_def image_def vimage_def
by force

value "arg_max' id {0::nat,2,3,1234}"

fun prova where 
"prova f X 0 = X" |
"prova f X (Suc n) = f n (prova f X n)"

lemma assumes 
"f 0=id" 
"(f 1)=arg_max' (proceeds b)"
shows
"winningAllocationsRel N G b = 
prova 
f (possibleAllocationsRel N G) (2::nat)"
using assms prova_def sorry

value "Random.next (1,1)"

value "Random.pick [(1::natural,10::nat),(2,12),(3,13)] 3"

term "Limited_Sequence.single"

value "Random_Sequence.single (1::nat)"

end

