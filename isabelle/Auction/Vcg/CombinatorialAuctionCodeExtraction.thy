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

header {* VCG auction: Scala code extraction *}

theory CombinatorialAuctionCodeExtraction

imports
CombinatorialAuction

(* The following three theories are needed for the extraction of Scala code *)
"~~/src/HOL/Library/Code_Target_Nat" 
"~~/src/HOL/Library/Code_Target_Int" 
"~~/src/HOL/Library/Code_Numeral"

begin

(* Next we define some auxiliary functions to facilitate pretty printing in Scala *)
(* allocationPrettyPrint transforms sets into lists *)
definition "allocationPrettyPrint a = 
   {map (%x. (x, sorted_list_of_set(a,,x))) ((sorted_list_of_set \<circ> Domain) a)}"

(* We define bids in Scala as lists of three elements: (participants, goods, bid). To use our
   vcga algorithm we need the bid vector to be a function from pairs (participant, {goods}) to
   the corresponding bid. Bid2funcBid does this conversion. singleBidConverter is a corresponding
   helper function. *)

abbreviation "singleBidConverter x == ((fst x, set ((fst o snd) x)), (snd o snd) x)"
definition "Bid2funcBid b = set (map singleBidConverter b) Elsee (0::integer)"

(* participantsSet extracts the participants from a bid vector. *)
definition "participantsSet b = fst ` (set b)"

(* goodsList extracts the goods from a bid vector. *)
definition "goodsList b = sorted_list_of_set (Union ((set o fst o snd) `(set b)))"

(* payment is a wrapper to reuse the allocation so that it is computed only once. *)
definition "payments b r n (a::allocation) = 
            vcgpAlg ((participantsSet b)) (goodsList b) (Bid2funcBid b) r n (a::allocation)"

(* Isabelle will export code for the vcgaAlg and payments as well as all other functions
   necessary for the computation and write it to a file of choice, in this case, for Linux
   the temporary file /dev/shm/VCG.scala *)
export_code vcgaAlg payments allocationPrettyPrint in Scala module_name VCG 
            file "/dev/shm/VCG-withoutWrapper.scala"

end

(* At this moment in time the code generated works well under Linux. However, there is a naming
   conflict in Windows originating from conflating nat and Nat as well as sup_set and Sup_set. 
   In order to make the code runnable under Windows as well, it is possible to universally
   replace, e.g., Nat by NNat and Sup_set by SSup_set. The following shell command may be 
   helpful with that. *)
(* 
{ { echo asdff; tac VCG-withoutWrapper.scala ; } | 
    sed -n -e '1,/\}/ !p'  | 
    tac | 
    cat - ../addedWrapper.scala; echo \}; }| 
    sed -e "s/\(Nat\)\([^a-zA-Z]\)/NNat\2/g; s/\(Sup_set\)\([^a-zA-Z]\)/SSup_set\2/g" >
    VCG.scala
*)


