theory DynamicAuctionCodeExtraction
imports
Trust2
"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Target_Numeral"

begin



definition "evaluateMe (input(*::(integer list => integer list)*)) 
(output(*::(_ => integer list)*))
= snd (output (String.implode ''Starting\<newline>Input the number of bidders:'', [])
, dynamicAuction input output)"
term evaluateMe

definition "evaluateMe2 
(input :: _)
(output:: _) 
= snd (output (
String.implode ''Starting\<newline>Input the number of bidders:'', True, []),
dynamicAuction input output)"
 

(* 
input and output will be the only manually written Scala functions 
(and will be passed as arguments to evaluateMe as the only action of the main method of our Scala wrapper ) 
- input will take a list as an argument, and grow it by the input (side effect) provided by the user.
- output will take a pair (list, messageAfterEachBid) as an argument, will return list without touching it, 
while printing messageAfterEachBid to the user (side effect).
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


export_code fst snd evaluateMe evaluateMe2 in Scala module_name a file "/dev/shm/a.scala"
end

