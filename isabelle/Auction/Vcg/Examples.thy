
(*
value "injections_alg [0::nat,1] {11::nat, 12}"
thy_deps

theorem counterexample_allocationDisjoint: assumes "a \<in> allocationsUniverse" 
"n1\<in> Domain a" "n2 \<in> Domain a"
shows "a,,,n1 \<inter> a,,,n2={}" nitpick
value "vcgaAlg (int`N00) \<Omega>00 (b00 Elsee 0) 1" 
*)


(* MC: test examples, commented out 
definition "N00 = {1,6::nat}"
definition "\<Omega>00 = [11::nat, 12, 13]"
definition "b00 = 
{
((1::nat,{11::nat}),3::nat),
((1,{12}),0),
((1,{11,12}),4),
((2,{11}),2),
((2,{12}),2),
((2,{11,12}),1)
}"
term b00
(* definition "example = vcgaAlg (int`N00) \<Omega>00 (b00 Elsee 0) 1" *)
definition ao where "ao=(%x. (if x=0 then (24::nat) else 11))"

value "randomBidsAlg {1,2,3} [11,12,13] (b01 Elsee 0) 1 (2,{12})" 
definition "N01={1::integer,2,3}"
definition "\<Omega>01=[11::integer,12,13]"
definition "f01=b01 Elsee 0"
definition "evaluateMe01 = vcgaAlg N01 \<Omega>01 f01 1"
definition "evaluateMe02 = maximalStrictAllocationsAlg N01 \<Omega>01 f01"
definition "evaluateMe03 = randomBidsAlg N01 \<Omega>01 f01 1 (2,{12})"
value "chosenAllocationAuxiliary (N01\<union>{seller}) \<Omega>01 f01 1" 
definition "chosenAllocationAuxiliary01={(2, {12}), (3, {13, 11})}"
(* value "graph ((N01\<union>{seller}) \<times> (Pow (set \<Omega>01)-{{}})) (randomBidsAlg N01 \<Omega>01 f01 1)" *) 
abbreviation "graphRandomBids01::((integer \<times> integer set) \<times> nat) set ==
{((3, {12, 13}), 1), ((3, {12}), 0), ((3, {}), 0), ((3, {13}), 1), ((3, {11, 13}), 2), ((3, {11}), 1),
  ((3, {11, 12}), 1), ((3, {11, 12, 13}), 2), ((2, {12, 13}), 1), ((2, {12}), 1), ((2, {}), 0), ((2, {13}), 0),
  ((2, {11, 13}), 0), ((2, {11}), 0), ((2, {11, 12}), 1), ((2, {11, 12, 13}), 1), ((1, {12, 13}), 0),
  ((1, {12}), 0), ((1, {}), 0), ((1, {13}), 0), ((1, {11, 13}), 0), ((1, {11}), 0), ((1, {11, 12}), 0),
  ((1, {11, 12, 13}), 0), ((seller, {12, 13}), 0), ((seller, {12}), 0), ((seller, {}), 0), ((seller, {13}), 0),
  ((seller, {11, 13}), 0), ((seller, {11}), 0), ((seller, {11, 12}), 0), ((seller, {11, 12, 13}), 0)}"
value "graph ((N01\<union>{seller}) \<times> (Pow (set \<Omega>01)-{{}})) (tiebidsAlg 
chosenAllocationAuxiliary01 
N01 (set \<Omega>01))"
(* 
MC: A key hint is in the much longer evaluation time of the following, compared to the one above
MC: fixed by changing "abbreviation tiebidsAlg ..." into "definition tiebidsAlg ..."
*)
value "graph ((N01\<union>{seller}) \<times> (Pow (set \<Omega>01)-{{}})) (tiebidsAlg 
(chosenAllocationAuxiliary (N01\<union>{seller}) \<Omega>01 f01 1) N01 (set \<Omega>01))"

value "vcgaAlg N01 \<Omega>01 f01 1"
value "b01 \<union> {}"

*)

abbreviation "goods == sorted_list_of_set o Union o Range o Domain"
(*
abbreviation "b02==b01 \<union> ({1,2,3}\<times>{{14},{15}})\<times>{20}"
abbreviation "N02==participants b02"
abbreviation "\<Omega>02==goods b02"
abbreviation "f02==b02 Elsee 0"

(*value "chosenAllocationAuxiliary (N02\<union>{seller}) \<Omega>02 f02 1"
value "maximalStrictAllocationsAlg (N02\<union>{seller}) \<Omega>02 f02"*)
abbreviation "chosenAllocationAuxiliary02==
{(2, {14}), (3, {15}), (1, {12, 13, 11})}" 
value "graph ((N02\<union>{seller}) \<times> (Pow (set \<Omega>02)-{{}}))
(tiebidsAlg chosenAllocationAuxiliary02 (participants b02) (set (goods b02)))"
(*value "graph ((N02\<union>{seller}) \<times> (Pow (set \<Omega>02)-{{}}))
(tiebidsAlg (chosenAllocationAuxiliary (N02\<union>{seller}) \<Omega>02 f02 1) (participants b02) (set (goods b02)))"*)
(*value "graph ((N02\<union>{seller}) \<times> (Pow (set \<Omega>02)-{{}}))
(resolvingBidAlg (N02\<union>{seller}) \<Omega>02 f02 1)"*) 
(* value "randomBidsAlg ((fst o fst)`b02) (sorted_list_of_set (Union ((snd o fst)`b02))) (b02 Elsee 0) 1 (1,{11})" *)
*)

(* part to make input/output easier *)
abbreviation "allocationPrettyPrint2 a == map (%x. (x, sorted_list_of_set(a,,x))) ((sorted_list_of_set \<circ> Domain) a)"
definition "helper (list) == (((hd\<circ>hd) list, set (list!1)), hd(list!2))"
definition "listBid2funcBid listBid = (helper`(set listBid)) Elsee (0::integer)"

abbreviation "singleBidConverter x == ((fst x, set ((fst o snd) x)), (snd o snd) x)"
definition "Bid2funcBid b = set (map singleBidConverter b) Elsee (0::integer)"

abbreviation "participantsSet b == fst ` (set b)"
abbreviation "goodsList2 b == sorted_list_of_set (Union ((set o fst o snd) `(set b)))"

definition "allocation b r = {allocationPrettyPrint2 
(vcgaAlg ((participantsSet b)) (goodsList2 b) (Bid2funcBid b) r)
}"

definition "payments b r = vcgpAlg ((participantsSet b)) (goodsList2 b) (Bid2funcBid b) r"
export_code allocation payments chosenAllocationAlg in Scala module_name VCG file "/dev/shm/VCG.scala"





abbreviation "b01 == 
{
((1::integer,{11::integer, 12, 13}),20::integer),
((1,{11,12}),18),
((2,{11}),10),
((2,{12}),15),
((2,{12,13}),18),
((3,{11}),2),
((3,{11,12}),12),
((3,{11,13}),17),
((3,{12,13}),18),
((3,{11,12,13}),19),
((4,{11,12,13,14,15,16}),19)
}"
value "participants b01"
(*
MC: Why does this 
value "maximalStrictAllocationsAlg {1,2,3} [11, 12, 13]
 (%x. (0::integer))"
take longer than this?
value "maximalStrictAllocationsAlg {1,2,3} [11, 12, 13]
 (b01 Elsee 0)"
*)
(* value "allAllocationsAlg3 {1,2,3,4,5,6,7,8} [11, 12, 13, 14, 15, 16, 17, 18, 19]"*)

end

(* 
{ { echo asdff; tac ../VCG.scala ; } | sed -n -e '1,/\}/ !p'  | tac | cat - ../addedWrapper.scala; echo \}; }| sed -e "s/\(Nat\)\([^a-zA-Z]\)/NNat\2/g; s/\(Sup_set\)\([^a-zA-Z]\)/SSup_set\2/g"
*)

