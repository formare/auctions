theory Trust

imports
t
(* "../Vcg/MiscTools" 
 "~/afp/Lazy-Lists-II/LList2" 
 "~/afp/XML/Xmlt" 
 "~~/src/HOL/ex/Iff_Oracle"
"~~/src/HOL/Library/Float"
 *)
"~/afp/Coinductive/Coinductive_List"
"~/afp/Show/Show_Instances"
Predicate

"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Target_Numeral"
(* "~~/src/HOL/Library/Code_Binary_Nat" *)
"~~/src/HOL/Library/Code_Numeral"
"~~/src/HOL/Library/Code_Char"
"~~/src/HOL/UNITY/ListOrder"
"~~/src/HOL/Library/Formal_Power_Series"
begin

abbreviation "currentBidder l == (size l - (2::nat)) mod (l!0)" (* the first bidder has label 0 *)
abbreviation "nextBidder l == (size l - (1::nat)) mod (l!0)"
abbreviation "currentRound l == (size l - (2::nat)) div (l!0)" (* the first round has label 0 *)
abbreviation "roundForNextBidder l == (size l - (1::nat)) div (l!0)"
abbreviation "E01 == [3::nat, 1, 2, 3, 4, 5, 6, 7, 8, 9, 7, 8, 9, 10 ,10, 10, 10, 10, 10, 11, 10]"

abbreviation "pickParticipantBids l i == sublist l
(((op +) (Suc i))`(((op *) (l!0))`{0..(currentRound l)}))"
abbreviation "pickRoundBids l i == sublist l {Suc(i*(l!0))..(Suc i)*(l!0)}"
abbreviation "listToGraph l == graph {0..<size l} (nth l)"
abbreviation "listToBidMatrix (l::nat list)==
listToGraph 
(
map (\<lambda>i. zip (replicate ((currentRound l)+1) True) (pickParticipantBids l i))
[(0::nat)..<(l!0)]
)"

lemma assumes "Suc n<size l" shows "(l!n = l!(Suc n)) = (sametomyleft l)!(Suc n)" 
using assms unfolding sametomyleft_def by fastforce

value "listToBidMatrix E01"

definition "message l = ''Current winner: '' @ 
(Show.show (maxpositions (pickRoundBids l (currentRound l)))) @ 
''Liveliness: '' @ Show.show(livelinessList (listToBidMatrix l)) @ ''\<newline>'' @ 
''Next, input bid for round ''@Show.show(roundForNextBidder l)@'', participant ''@(Show.show(nextBidder l))"
(*
value "int_of_string ''123''"
definition trusted where "trusted (output::(String.literal => _)) (input::(integer  => _)) = 
(output (String.implode ''zio''), input 0)"
*)

(*
definition "prova (input::(integer => String.literal)) 
(output::(String.literal => String.literal))
= (output (String.implode ''start''), (inf_llist (output o String.implode o
concat o (tolist (String.explode o input \<circ> integer_of_nat))
)))"
*)

definition "prova (input::(integer => String.literal)) (output::(String.literal => String.literal))
= inf_llist (output o id o input \<circ> integer_of_nat)"
(* MC: This approach ignores the argument given to input, giving a thinner wrapper.
I couldn't find a way to preserve the previous history of inputs, in this way, however.
Hence we use evaluateMe below.*)
(*
definition "evaluateMe (input::(String.literal list => String.literal list)) 
(output::(String.literal list \<times> String.literal => String.literal list))
= (output ([], String.implode ''Starting\<newline>Input the number of bidders:''), 
iterates (output o (%x. (x,String.implode (concat (map String.explode x)))) o input) [])"
*)

definition "evaluateMe (input::(integer list => integer list)) 
(output::(integer list \<times> String.literal => integer list))
= (output ([], String.implode ''Starting\<newline>Input the number of bidders:''), 
iterates (output o 
(%x. (x,String.implode(message (map nat_of_integer x)))) o (%l. (tl l) @ [hd l]) 
o input) [])"

(*
definition "evaluateMe (input::(integer list => integer list)) 
(output::(integer list \<times> String.literal => integer list))
= (output ([], String.implode ''Starting\<newline>Input the number of bidders:''), 
iterates (output o 
(%x. (x,String.implode (concat (map (Show.show \<circ> int_of_integer) x)))) 
o (%l. (tl l) @ [hd l]) o input) [])"
*)
(* 
input and output will be the only manually written Scala functions 
(and will be passed as arguments to evaluateMe as the only action of the main method of our Scala wrapper ) 
- input will take a list as an argument, and grow it by the input (side effect) provided by the user.
- output will take a pair (list, message) as an argument, will return list without touching it, 
while printing message to the user (side effect).
Thus, iterating the combined function output o XXX o input (where XXX is the Isabelle function doing 
the ``real work''), evaluateMe will provide a dynamic auction execution.
The length of the list passed to XXX will be used to determine in which round we are.

Thus, the manually-written Scala code (to be appended to the Isabelle-generated lines) will be:
*)

(*
def untrustedInput(n:List[String]) : List[String] = {
	val x=readLine;
	return (x::n);
}

def untrustedOutput(x: (List[String], String)) : List[String] = {
	println(snd (x));
	return (fst (x));
}

def main(args: Array[String]) {
	val x=evaluateMe(untrustedInput, untrustedOutput);
}

*)

(*
It can't probably get thinner than this.
My ambition would be to handle everything besides input/output from inside Isabelle, including
conversion from strings (as from input) to numbers and viceversa (for output); 
this is definitely possible, but how realistic given our schedule?
We could momentarily choose to directly use Scala integers as input/output, 
which is less robust/flexible/elegant but simpler.
*)

export_code fst snd evaluateMe in Scala module_name a file "/dev/shm/a.scala"

find_consts "real set => real"
term listrel
value "maxpositions [1::nat,3, 2,3]"

abbreviation "sublistAccordingTo list boolList == sublist list (set (filterpositions2 (%x. x=True) boolList))"
value "sublistAccordingTo [1,2,3::int] [True,False,True]"

fun valid where "valid step [] = []" |
"valid step (x#xs) = (
(card((set (maxpositions (sublistAccordingTo xs (valid step xs))))) \<ge> 2 & (x=Max (set 
(sublistAccordingTo xs (valid step xs))
))) 
\<or>
(card((set (maxpositions (sublistAccordingTo xs (valid step xs))))) = 1 & (x\<ge>Max (set 
(sublistAccordingTo xs (valid step xs))
) + step))
\<or>
(xs = [] & (x \<ge> 0))

)#(valid step xs)"
value "card((set (maxpositions [1::int,2,3,2,3]))) \<ge> 1"
value "valid (-1::int) [1, 2, 3, 4]"

abbreviation "isGrowing step l == (\<forall>n\<in>{0..<size l}. l!(Suc n) - (l!n)\<ge>step)"

abbreviation "pairWise Op l m == [Op (l!i) (m!i). i <- [0..<min (size l) (size m)]]"
lemma lm01: assumes "n\<in>{0..<min (size l) (size m)}" shows "(pairWise Op l m)!n = Op (l!n) (m!n)"
using assms by auto
abbreviation "deltaBids (*step*) l == (* step # *) (pairWise (op -) (tl l) l)"
value "filterpositions2 (%x. x>3) [1::nat,2]"
lemma lm02: "min (size (tl l)) (size l)=size l - (1::nat)" by simp
lemma lm03: assumes "n\<in>{0..<size (l::int list)-(1::nat)}" shows "(deltaBids l)!n=(l!(Suc n)) - ((l!n)::int)" using 
assms lm02 length_tl nth_tl atLeastLessThan_iff diff_zero monoid_add_class.add.left_neutral 
nth_map_upt by (metis (erased, lifting))
abbreviation "firstInvalidBidIndex step l == 
1 + hd (filterpositions2 (%x. x<step) (deltaBids (*step*) l)@[size l])"

lemma fixes f::"nat => real" shows "setsum (%x. f (x+1) - f x) {0..<Suc n}=f (Suc n) - f 0"
using assms setsum_natinterval_difff setsum_Suc_diff sorry


lemma assumes "size (l::int list)\<ge>2" shows "listsum [l!(n+1)-(l!n). n<-[0..<size l - (1::nat)]]=l!(size l - (1::nat))-(l!0)"
using assms setsum_natinterval_difff setsum_Suc_diff sorry

lemma assumes "size l\<ge>2" shows "l!(size l-(1::nat))=listsum (deltaBids l) + ((l!0)::int)"
using assms lm03 sorry

abbreviation "amendedbidlist3 step l == update2 l {firstInvalidBidIndex step l..<size l} (%x. 
l!(firstInvalidBidIndex step l - 1))"

lemma assumes "step \<ge>(1::nat)" "firstInvalidBidIndex step (l::nat list)=Suc 0" shows 
"l!0 \<ge> 0*step" using assms by presburger

lemma assumes "step \<ge>(1::nat)" "firstInvalidBidIndex step (l::nat list)=Suc (Suc n)"
"\<forall>m\<le>n. firstInvalidBidIndex step (l::nat list)=Suc m \<longrightarrow> l!m\<ge>m*step" shows
"l!(Suc n)\<ge>(Suc n)*step" using assms filterpositions2_def sorry

lemma assumes "l\<noteq>[]" "step \<ge>(1::nat)" "firstInvalidBidIndex step (l::nat list)=Suc n" shows 
"!m<n. (deltaBids l)!m \<ge> step " using assms nth_def using filterpositions2_def sorry

lemma assumes "step \<ge>(1::nat)" "firstInvalidBidIndex step (l::nat list)=Suc n" shows 
"l!n \<ge> n*step + (l!0)" using assms filterpositions2_def lm01 lm02 lm03 
setsum_natinterval_difff setsum_Suc_diff sorry


abbreviation "EX02 == [0::nat, 2, 4, 6, 8, 11, 12, 11]"
value "firstInvalidBidIndex 2 EX02"
value "amendedbidlist3 2 EX02"

abbreviation "setOfAllowedBids step l == {x. x=Max (set l) \<or> (isGrowing step l \<and> x \<ge> step+Max (set l))}"
value "Example02"
value "amendedbidlist (Example02,,20)"

lemma assumes "(step::nat) \<ge> 1" "\<forall>l\<in>(X::nat list set). set l \<subseteq> {0..0}" shows "EX n. \<forall>l. l \<in> X \<longrightarrow> firstInvalidBidIndex step l < n" 
using assms 
using filterpositions2_def sorry

lemma assumes "(step::nat) \<ge> 1" "\<forall>l\<in>(X::nat list set). set l \<subseteq> {0..N}" shows "EX n. \<forall>l. l \<in> X \<longrightarrow> firstInvalidBidIndex step l < n"
using assms 
unfolding filterpositions2_def

lemma assumes "\<forall>l\<in>X. set l \<subseteq> {0..N}" 
shows "EX M n. \<forall> l\<in> X. (\<forall>m. (m > n & m < size l) \<longrightarrow> ((amendedbidlist3 step l)!m = M))"
using assms sorry

(* abbreviation "allowedBids bidSet bid == " activity rule*)

end

