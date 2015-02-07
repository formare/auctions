(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Author: Marco B. Caminati http://caminati.co.nr

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

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
(* definition "b1 = [[[1::integer], [11,12,13], [3]], [[2],[11,13],[22]]]" *)
definition "b1 = [
[[1::integer], [11,12], [2]], 
[[2], [11], [2]],
[[2], [12], [2]],
[[3], [11], [2]],
[[3], [12], [2]]
]"
term Nat
(* [[1::integer], [10,20,30,40], [3]] \<longrightarrow> (1, {10,20,30,40), 3*)
definition "helper (list) == (((hd\<circ>hd) list, set (list!1)), hd(list!2))"
definition "listBid2funcBid listBid = (helper`(set listBid)) Elsee (0::integer)"
term "a::natural"
(* definition "converter z = (integer_of_int (fst z), snd z)" *)
abbreviation "converter==id"
abbreviation "participantsList == remdups o (map (hd\<circ>hd))"
abbreviation "goodsList == remdups \<circ> concat \<circ> (map (% l. l!1))"
abbreviation "allocationPrettyPrint a == (%z. (fst z, sorted_list_of_set (snd z)))`a"
abbreviation "allocationPrettyPrint2 a == map (%x. (x, sorted_list_of_set(a,,x))) ((sorted_list_of_set \<circ> Domain) a)"
term "folding.F insort []"
definition mbca :: "'a set => 'a list" where "mbca=folding.F (insort_key (\<lambda>x. 1::nat)) []"
definition mbcb where "mbcb=folding.F (insort_key fst) []"
definition "randomNumber=1"
abbreviation "maximalStrictAllocationsList N G b==
argmaxList (setsum b) (allStrictAllocations ({seller}\<union>N) G)"
abbreviation "winningAllo == hd (maximalStrictAllocationsList 
(set (participantsList b1)) (goodsList b1) (listBid2funcBid b1)
)"
value winningAllo
definition "example = {allocationPrettyPrint2 winningAllo}"
value example
definition "paymentFunc n = 
Max (setsum 
(listBid2funcBid b1)
 ` (allAllocationsComp (
(set (participantsList b1))
-{n}) 
(goodsList b1)
)) - (setsum 
(listBid2funcBid b1)
(winningAllo -- n))"

definition "paymentList=[paymentFunc n. n<-participantsList b1]"

export_code example paymentList in Scala module_name a file "/dev/shm/a.scala"

(* definition "example = converter`(vcgaAlg ((set N01)) G01 ((listBid2funcBid b1)\<circ>converter) 1)" 
definition "example2=eval_rel example" *)
(*


value "
allocationPrettyPrint2`
(maximalStrictAllocations (set (participantsList b1)) (goodsList b1) (listBid2funcBid b1))"
value "vcgpAlg (set (participantsList b1)) (goodsList b1) (listBid2funcBid b1) 1 2"
*)
value "goodsList b1"
value "nat_of_integer (-1)"

abbreviation "aOutside X R == R - (X \<times> Range R)"
(*abbreviation "aOutside X R == R || (-X)"*) (*MC: this doesn't output nicely*)
lemma "R outside X = R||-X" unfolding Outside_def restrict_def by fast
definition swappedOutside 
(* (infix "aoutside" 75) *) 
where "swappedOutside R X = aOutside X R"
notation swappedOutside (infix "aoutside" 75) 

value "{(1::int,3), (2,4::nat)} aoutside {1}"
value "Outside  {(1::int,3), (2,4::nat)} {1}"


end

