(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory DynamicAuctionCodeExtraction
imports
DynamicAuctionNonTerminating
DynamicAuctionTerminating
"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int"
"~~/src/HOL/Library/Code_Target_Numeral"

begin

(* 
  input and output will be the only manually written Scala functions 
  (and will be passed as arguments to dynamicAuctionNonTerminatingExported or 
   dynamicAuctionTerminatingExported respectively. input and output are the only action of the 
   main method of the Scala wrapper ) 
- input will take a list as an argument, and grow it by the input (side effect) provided by the user.
- output will take a pair (list, messageAfterEachBid) as an argument, will return list without touching it, 
while printing messageAfterEachBid to the user (side effect).
Thus, iterating the combined function output o XXX o input (where XXX is the Isabelle function doing 
the ``real work''), evaluateMe will provide a dynamic auction execution.
The length of the list passed to XXX will be used to determine in which round we are.

Thus, the manually-written Scala code (to be appended to the Isabelle-generated lines) will be:
*)

definition "dynamicAuctionNonTerminatingExported (input ::(integer list => integer list)) 
                                                 (output :: _ => integer list) = 
            snd (output (String.implode ''Starting\<newline>Input the number of bidders:'', []),
                 dynamicAuctionNonTerminating input output)"

definition "dynamicAuctionTerminatingExported  (input :: _)  (output:: _) = 
            snd (output ( String.implode ''Starting\<newline>Input the number of bidders:'', True, []),
                 dynamicAuction input output)"

export_code fst snd dynamicAuctionTerminatingExported in Scala 
            module_name dynamicAuctionTerminating 
            file "/dev/shm/dynamicAuctionTerminating.scala"

export_code fst snd dynamicAuctionNonTerminatingExported in Scala 
            module_name dynamicAuctionNonTerminating
            file "/dev/shm/dynamicAuctionNonTerminating.scala"

end

