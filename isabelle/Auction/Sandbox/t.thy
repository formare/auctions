theory t
imports Main 
"~~/src/HOL/Library/Code_Target_Nat"
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

end

