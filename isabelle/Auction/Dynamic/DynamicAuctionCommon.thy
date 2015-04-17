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


theory DynamicAuctionCommon

imports

"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/afp/Show/Show_Instances"
"../Vcg/MiscTools"

begin

(* tolist creates a list of the application of f to 0 ... n-1, i.e., [f 0, f 1, ..., f (n-1)] *)
abbreviation "tolist f n == map f [0..<n]"  

text{*{@term updateList} alters the entries of the list {@term l} having indices in {@term X} 
by applying {@term f} to each such index. E.g. if f squares a number
updateList [1, 2, 3, 4, 5, 6] {2, 3} (\<lambda>x. x*x) results in [1 2 4 9 5 6].}*}
abbreviation "updateList l X f == tolist (override_on (nth l) f X) (size l)"

(* The following two type synomyms are used to make the theory better readable. participants
   and prices are represented by nat. *)
type_synonym participant = nat
type_synonym price = nat

(* unzip1 and unzip 2 take a list of pairs and extract a list of the first elements and second 
   elements, respectively *)
abbreviation "unzip1 == map fst"
abbreviation "unzip2 == map snd"



(* sameToMyLeft takes a list and returns a list of bool of the same length checking whether the
   element is equal to its left neighbour (starting with False, since the zeroth element has
   no left neighbour). *)
definition sameToMyLeft 
  where "sameToMyLeft l = take (size l) (False # [fst x = snd x. x <- drop 1 (zip l ((0) # l))])" 

(* Variant of the above, easier for some proofs *)
abbreviation "sameToMyLeft' l == [ (i \<noteq> 0 & (l!i = l!(i-(1)))). i <- [0..<size l]]"

lemma lm01: 
  assumes "Suc n < size l" 
  shows "(l!n = l!(Suc n)) = (sameToMyLeft l)!(Suc n)" 
  using assms unfolding sameToMyLeft_def by fastforce

lemma lm02: 
  assumes "Suc n < size l" 
  shows "(l!n = l!(Suc n)) = (sameToMyLeft' l)!(Suc n)" 
  using assms by force

lemma lm03: 
  assumes "0 < size l" 
  shows "(sameToMyLeft' l) ! 0 = False & (sameToMyLeft l) ! 0 = False" 
  unfolding sameToMyLeft_def using assms by auto

lemma sameToMyLeftLength: 
  "size (sameToMyLeft l) = size l & size (sameToMyLeft' l)=size l" 
  unfolding sameToMyLeft_def by simp

lemma sameToMyLeftEquivalence: 
  assumes "i < size l" 
  shows "(sameToMyLeft l) ! i = (sameToMyLeft' l) ! i"   
proof -
  have "i = 0 \<or> (EX j. (i = Suc j))" by presburger
  then show ?thesis using assms lm01 lm02 lm03 by blast
qed

(* l is a list of bids from a single bidder. stopAuctionAt checks whether the bidder has terminated
   bidding. This is the case iff the bid is the same as in the previous round. filterpositions2
   is defined in Argmax.thy. It computes the positions in a list for which a predicate is true.  *)
definition stopAuctionAt 
 where "stopAuctionAt l = filterpositions2 (%x. (x = True)) (sameToMyLeft' l)"

(* B is a matrix containing all bids of all bidders. stops B returns all the round numbers
   in which all bidders do not change their bids anymore. *)
definition "stops B = \<Inter> {set (stopAuctionAt (unzip2 (B,,i)))| i. i \<in> Domain B}"

(* B is a matrix containing all bids of all bidders. stopAt B returns the minimal round number
   in which all bidders do not change their bids anymore. *)
definition "stopAt B = Min (stops B)" 

(* duration computes the number of rounds in B *)
abbreviation "duration B == Max (size ` (Range B))"

(* For a bid matrix B such as
   abbreviation "B0 == {(1::participant,[(True,1::price),(True, 2),(True, 3),(True, 4), (True, 4)]),
                    (2::participant,[(True,1::price),(True, 2),(True, 3),(True, 4), (True, 4)]),
                    (3::participant,[(True,2::price),(True, 3),(True, 4),(True, 5), (True, 5)])}"
   livelinessList B is a list of boolean values such that the value at position i indicates that
   the auction is alive in round i.
*)
definition "livelinessList B = 
            True # updateList (replicate (duration B) True) (stops B) (%x. False)"

(* l is a flat list of all bids of all participants with the first element of the list representing
   the number of participants n, then the next n elements represent the bids of the first round
   for each participants and so on. E.g., (3 1 2 2 2 3 3 4 5 5) means there are 3 participants who
   bid in the first round 1, 2, and 2, respectively, in the second 2, 3, 3, and 
   in the third 4, 5, 5 *)

(* l!0 is the number of participants, currentBidder computes the bidder wrt the last bid given.*)
abbreviation "currentBidder l == (size l - (2::nat)) mod (l!0)"

(* nextBidder is the bidder after the currentBidder *)
abbreviation "nextBidder l == (size l - (1::nat)) mod (l!0)"

(* the currentRound of bidding starting from 0 *)
abbreviation "currentRound l == (size l - (2::nat)) div (l!0)"

(* The round in which the next bid will be.*)
abbreviation "roundForNextBidder l == (size l - (1::nat)) div (l!0)"


(* pickParticipantBids l i extracts the bids of participant i *)
abbreviation "pickParticipantBids l i == 
              sublist l (((op +) (Suc i)) 
                         `(((op *) (l!0))  `{0..(currentRound l)}))"

(* pickRoundBids extracts the bids in round i, starting with counting from 0 *)
abbreviation "pickRoundBids l i == sublist l {Suc(i*(l!0))..(Suc i)*(l!0)}"

(* listToGraph transforms a list into a function from indices to values in a set theoretical form, 
   e.g. with l0 = l0 == [3::nat, 1, 1, 2, 2, 3, 4, 4, 6, 5] you get
   "{(0, 3), (1, 1), (2, 1), (3, 2), (4, 2), (5, 3), (6, 4), (7, 4), (8, 6), (9, 5)}" *)
abbreviation "listToGraph l == graph {0..<size l} (nth l)"

(* listToBidMatrix creates from a flat of bids a bidMatrix in which the activity flag of a bidder
   is always True, e.g, with "l0 == [3::nat, 1, 1, 2, 2, 3, 4, 4, 6, 5]" we get: 
   "{(0, [(True, 1), (True, 2), (True, 4)]), 
     (1, [(True, 1), (True, 3), (True, 6)]),
     (2, [(True, 2), (True, 4), (True, 5)])}"*)
abbreviation "listToBidMatrix (l::nat list)==
              listToGraph (map (\<lambda>i. zip (replicate ((currentRound l) + 1) True) 
                                        (pickParticipantBids l i))
                           [(0::nat)..<(l!0)])"

(* messageAfterEachBid is a string which informs the next bidder about the current winner, the liveliness information plus a request for their next bid. *)
definition "messageAfterEachBid l = 
            ''Current winner: '' @ 
            (Show.show (maxpositions (pickRoundBids l (currentRound l)))) @ 
            ''\<newline>'' @ 
            ''Liveliness: '' @ 
            Show.show(livelinessList (listToBidMatrix l)) @ 
            ''\<newline>'' @ 
            ''Next, input bid for round ''@Show.show(roundForNextBidder l)@
            '', participant '' @
            (Show.show(nextBidder l))"


end

