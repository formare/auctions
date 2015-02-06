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

begin
term stopat
term alive

abbreviation "currentRound l == (size l - (2::nat)) div (l!0)" (* the first round has label 0 *)
abbreviation "nextRound l == (size l - (1::nat)) div (l!0)"
abbreviation "currentBidder l == (size l - (2::nat)) mod (l!0)" (* the first bidder has label 0 *)
abbreviation "nextBidder l == (size l - (1::nat)) mod (l!0)"

abbreviation "E01 == [3::nat, 1, 2, 3, 4, 5, 6, 7, 8, 9, 7, 8, 9, 10 ,10, 10, 10, 10, 10, 11, 10]"

abbreviation "pickParticipantBids l i == sublist l
(((op +) (Suc i))`(((op *) (l!0))`{0..(currentRound l)}))"
abbreviation "pickRoundBids l i == sublist l {Suc(i*(l!0))..(Suc i)*(l!0)}"
value "pickRoundBids E01 (currentRound E01)"
abbreviation "listToGraph l == graph {0..<size l} (nth l)"
abbreviation "listToBidMatrix (l::nat list)==
listToGraph 
(
map (\<lambda>i. zip (replicate ((currentRound l)+1) True) (pickParticipantBids l i))
[(0::nat)..<(l!0)]
)"

lemma assumes "Suc n<size l" shows "(l!n = l!(Suc n)) = (sametomyleft l)!(Suc n)" 
using assms unfolding sametomyleft_def by fastforce
value "stopat (listToBidMatrix E01)"
value "wdp (listToBidMatrix [3,1,3,5,1,21,2222,44,100,0])"
value "livelinessList (listToBidMatrix E01)"
definition "message l = ''Current winner: '' @ 
(Show.show (maxpositions (pickRoundBids l (currentRound l)))) @ 
''Liveliness: '' @ Show.show(livelinessList (listToBidMatrix l)) @ ''\<newline>'' @ 
''Next, input bid for round ''@Show.show(nextRound l)@'', participant ''@(Show.show(nextBidder l))"
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

find_consts "'a list => 'a list"

definition "evaluateMe (input::(integer list => integer list)) 
(output::(integer list \<times> String.literal => integer list))
= (output ([], String.implode ''Starting\<newline>Input the number of bidders:''), 
iterates (output o 
(%x. (x,String.implode(message (map nat_of_integer x)))) 
o (%l. (tl l) @ [hd l]) o input) [])"
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
this is definitely possible, but how realistic giving our schedule?
We could momentarily choose to directly use Scala integers as input/output, 
which is less robust/flexible/elegant but simpler.
*)

export_code fst snd evaluateMe in Scala module_name a file "/dev/shm/runme.scala"
value "Show.show (143::rat)"

end

