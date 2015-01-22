(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Author: Marco B. Caminati http://caminati.co.nr

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

header {* VCG auction: definitions and theorems *}

theory export

imports
(* Complex *)
(*"../Vcg/UniformTieBreaking"*)
"../Vcg/CombinatorialAuction"
"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int" 
(* "~~/src/HOL/Library/Code_Binary_Nat" *)
"~~/src/HOL/Library/Code_Numeral"
"~~/src/HOL/Library/Code_Char"

begin

definition "N01 = [1,2::integer]"
definition "G01 = [11::integer, 12, 13]"
definition "b01 = 
{
((1::nat,{11::nat}),3::nat),
((1,{12}),0),
((1,{11,12}),4),
((2,{11}),2),
((2,{12}),2),
((2,{11,12}),1)
}"
definition "B01 = (%x. if x=(2,{12}) then 2 else (0::nat))"
(* definition "example = vcgaAlg (int`N00) G00 (b00 Elsee 0) 1" *)
definition ao where "ao=(%x. (if x=0 then (24::nat) else 11))"
definition "b1 = [[[1::integer], [11,12,13], [3]], [[2],[11,13],[22]]]"
(* [[1::integer], [10,20,30,40], [3]] \<longrightarrow> (1, {10,20,30,40), 3*)
definition "helper (list) == (((hd\<circ>hd) list, set (list!1)), hd(list!2))"
definition "listBid2funcBid listBid = (helper`(set listBid)) Elsee (0::integer)"
term "a::natural"
definition "converter z = (integer_of_int (fst z), snd z)"
definition "example = converter`(vcgaAlg (int_of_integer`(set N01)) G01 ((listBid2funcBid b1)\<circ>converter) 1)"
definition "example2=eval_rel example"
value example
term vcgaAlg
export_code example in Scala module_name VCG file "/dev/shm/export.scala"
end

