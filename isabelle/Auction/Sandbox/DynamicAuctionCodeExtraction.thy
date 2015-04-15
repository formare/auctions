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

export_code fst snd evaluateMe evaluateMe2 in Scala module_name a file "/dev/shm/a.scala"
end

