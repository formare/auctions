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

abbreviation "mbc0 B == updateList (replicate (duration B) True) (stops B) (%x. False)"

(* abbreviation "B == {(1::participant,[1::price,2,3,4,4]),(2,[1,2,3,4,4]),(3,[2,3,4,5,5])}"*)
value "duration B"
(* value "stops B"

value "mbc0 B"
*)

definition "livelinessList B = True # updateList (replicate (duration B) True) (stops B) (%x. False)"
definition "alive (B::(participant \<times> (bool \<times> price) list) set) = nth (livelinessList B)"
abbreviation "AddSingleBid B part b == B +< (part, (B,,part)@[(True,b)])"
definition "addSingleBid (B::(participant \<times> ((bool \<times> price) list)) set) (part::participant) (b::price) = 
B +< (part, (B,,part)@[(True,b)])"
abbreviation "Example02 == {
(10::nat, zip (replicate (10::nat) True) 
[1::nat,6,4,1,2,2,2]),
(20, zip (replicate (10::nat) True) 
[5::nat,4,7,7,8,3,3,3])
}"
value "stops Example02"

abbreviation "Example03 == {
(10::nat, zip (replicate (10::nat) True) 
[1::nat,4,4,5,6,6,6,6,6,6]),
(20, zip (replicate (10::nat) True) 
[5::nat,4,7,7,9,9,9,9,9,9])
(*0,   ,1,2,3,4,5,6,7,8,9*)
}" (*MC: This means that bidder 10 always submits a True ("I'm game"), and the temporal sequence of bids 
1,4,4,5,6,6,6,6,6,6.
*)

(*abbreviation "nullBid == ([]::(bool \<times> price) list)"*)
abbreviation "BidMatrix == {(0::nat, ([]::(bool \<times> price) list)),(1::nat, [])}"
definition "bidMatrix = {(0::nat, ([]::(bool \<times> price) list)),(1::nat, [])}"
(*definition "bidMatrix = {(0::nat, ([(True,1)]::(bool \<times> price) list)),(1::nat, [(True,1)])}"*)
definition "example02=addSingleBid bidMatrix (0::nat) (4::nat)"
(* lemma "alive B 0 = True" using assms alive_def sorry *)

abbreviation "M00 == addSingleBid bidMatrix 0 0"
abbreviation "MM == addSingleBid M00 1 0"
abbreviation "MMM == addSingleBid MM 0 0"
abbreviation "MMMM == addSingleBid MMM 1 0"
value "livelinessList MM"

definition "(numberOfBidders::nat) = (card bidMatrix)"
definition "example=alive bidMatrix numberOfBidders"

(* CR: cur, prev implicitly defined; thus, they apply to any fixed number of bidders *)
definition liveliness' where "liveliness' prev cur = (if 
((snd cur) < (snd prev) \<or> \<not> (fst cur)) 
then False else True)"

definition lastvalidbid where 
"lastvalidbid prev cur = (if liveliness' prev cur then (snd cur) else (snd prev))"

fun amendedbid where
"amendedbid b 0 = (b!0)" |
"amendedbid b (Suc t) = 
(liveliness' (amendedbid b t) (b!(Suc t)), lastvalidbid (amendedbid b t) (b!(Suc t)))"

fun amendedbidlist where (*MC: this assumes that the list of bids grows on the left through time *)
"amendedbidlist [] = [(True, 0::nat)]" |
"amendedbidlist (x # b) = 
(liveliness' ((amendedbidlist b)!0) x, lastvalidbid ((amendedbidlist b)!0) x) # (amendedbidlist b)"

abbreviation "amendedbidlist2 b == rev (amendedbidlist (rev b))"

abbreviation "amendedbids B == B O (graph (Range B) amendedbidlist2)"

(*abbreviation "bidsattime B t == (snd o (%x. x!t))`(Range B)"*)
abbreviation "bidsattime B (t::nat) == B O (graph (Range B) (%x::((bool\<times>nat) list). snd (x!t)))"
definition "winner B = argmax (toFunction (bidsattime (amendedbids B) (stopAt (amendedbids B))))
(Domain (bidsattime (amendedbids B) (stopAt (amendedbids B))))"

value "amendedbids example03"
value "bidsattime (amendedbids example03) (stopAt example03)"
value "amendedbids example03 O (graph (Range (amendedbids example03)) (%x. snd (x!6)))"
value "stopAt (amendedbids example03)"
value "snd (nth (amendedbids example03,,20) 6)"
value "(% x. x!6)` ( Range (amendedbids example03))"
value "bidsattime (amendedbids example03) (stopAt (amendedbids example03))"
value "stopAt (amendedbids MMMM)"

(* MC: Not employed at the moment, could be used to model feedback to bidders 
for them to decide future bids based on how the auction's going *)
fun bid ::"('a list => 'a) => 'a list => 'a list"  where
"bid feedback []=[]" | "bid feedback (x#b) = (feedback (x#b))#b"

definition swap where "swap d = (% i. (%t. d t i))" 

abbreviation interface where "interface c == (nth (zip [t<0. t <- c] c))"

(*
abbreviation lastrounds where "lastrounds B == graph {1,2,3} (% i. 
set (stopAuctionAt ((map snd) (tolist 10 (amendedbid (B i))))))"

abbreviation example where 
"example == %t::instant. (if (t=0) then (True, 10::nat) else (True, 1))"

abbreviation lastround where "lastround B == Min (\<Inter> (Range  (lastrounds B)))"
*)

value "(filterpositions2 (%x. x = False) (livelinessList MMMM)) ! 0"
value "Max (*this is the tie breaker*)
 ((bidsattime MMMM ((Max (size ` snd ` MMMM)) - (1::nat))) (*This is the last bidvector *) ^-1 `` 
{Max (Range (bidsattime MMMM ((Max (size ` snd ` MMMM)) - (1::nat))))}
)" (* This is the winner *)
value "(bidsattime MMMM ((Max (size ` snd ` MMMM)) - (1::nat))),,
(Max (*this is the tie breaker*)
 ((bidsattime MMMM ((Max (size ` snd ` MMMM)) - (1::nat))) (*This is the last bidvector *) ^-1 `` 
{Max (Range (bidsattime MMMM ((Max (size ` snd ` MMMM)) - (1::nat))))}))" (* This is the price for winner *)
definition wdp where "wdp matrix =
Max ((bidsattime matrix ((Max (size ` snd ` matrix)) - (1::nat))) ^-1 `` 
{Max (Range (bidsattime matrix ((Max (size ` snd ` matrix)) - (1::nat))))})"
definition "price matrix =
(bidsattime matrix ((Max (size ` snd ` matrix)) - (1::nat))),,
(Max ((bidsattime matrix ((Max (size ` snd ` matrix)) - (1::nat)))^-1 `` 
{Max (Range (bidsattime matrix ((Max (size ` snd ` matrix)) - (1::nat))))}))"

definition "a1 matrix=bidsattime matrix ((Max (size ` snd ` matrix)) - (1::nat))"
definition "b1 matrix=
(Max ((bidsattime matrix ((Max (size ` snd ` matrix)) - (1::nat)))^-1 `` 
{Max (Range (bidsattime matrix ((Max (size ` snd ` matrix)) - (1::nat))))}))"

value "a1 MMMM"
value "(a1 MMMM),,(b1 MMMM)"
value "{(0, 0), (0, 0), (1, 0), (1, 0)},, (b1 MMMM)"
value "the_elem {0, 0}"
(* export_code alive addSingleBid bidMatrix n example example02 wdp price in Scala module_name Dyna file "/dev/shm/scala/Dyna.scala" *)

(*MC: first basic approach. We have bids for each (natural) instant, from which we calculate, at a given instant,
a pair (boolean, lastvalidprice).
The first is a flag liveliness saying whether that bidder is still into play, and can be freely set by the bidder himself.
But it also turn into false if the bid is invalid (which for the moment just coincides with the fact that his bid has decreased, 
but can be enriched with other conditions, like reserve price, minimal increase, etc...).
The second preserves the last valid bid, which for the moment coincides with the price of last time we computed a true flag. *)
end

