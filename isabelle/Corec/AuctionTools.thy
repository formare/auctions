theory AuctionTools
imports Main 
"~~/src/HOL/Library/Code_Target_Nat"
"~/afp/Vickrey_Clarke_Groves/MiscTools"

begin

fun update where "update l1 l2 [] = l1"| "update l1 l2 (x#xs) = list_update (update l1 l2 xs) x (l2!x)"
abbreviation "tolist f n == map f [0..<n]"  
abbreviation "update2 l X f == tolist (override_on (nth l) f X) (size l)"
text{*{@term update2} alters the entries of the list {@term l} having indices in {@term X} 
by applying {@term f} to each such index. }*}

type_synonym instant=nat 
type_synonym participant=nat
type_synonym price=nat
type_synonym newbid="instant => (bool \<times> price)"
type_synonym bids="instant => (participant => price)"
type_synonym submission="bool \<times> price"
type_synonym dynbid="submission list"
type_synonym dynbids="(instant \<times> dynbid) set"
(* abbreviation "toSubmission p == (True,p)" *)
abbreviation "unzip1 == map fst"
abbreviation "unzip2 == map snd"

(*MC: first basic approach. We have bids for each (natural) instant, from which we calculate, at a given instant,
a pair (boolean, lastvalidprice).
The first is a flag liveliness saying whether that bidder is still into play, and can be freely set by the bidder himself.
But it also turn into false if the bid is invalid (which for the moment just coincides with the fact that his bid has decreased, 
but can be enriched with other conditions, like reserve price, minimal increase, etc...).
The second preserves the last valid bid, which for the moment coincides with the price of last time we computed a true flag. *)

definition sametomyleft where (*MC: try to use rotate instead *)
(* "sametomyleft l = [fst x = snd x. x <- zip l (((hd l) + 1)# l)]" *)
"sametomyleft l = take (size l) (False # [fst x = snd x. x <- drop 1 (zip l ((0) # l))])" 

abbreviation "sametomyleft' l == [ (i \<noteq> 0 & (l!i = l!(i-(1)))). i <- [0..<size l]]"
definition "sametomyleft'' = sametomyleft'"

definition sametomyright where 
"sametomyright l = [fst x = snd x. x <- zip l (drop 1 l)]"
(* definition "sametomyleft l = take (size l) (False # (sametomyright l))" *)

definition stopauctionat2 where "stopauctionat2 f=Min (Domain ((graph UNIV (%t. f (t+1::nat))) \<inter> 
(graph UNIV f)))"

definition stopauctionat3 where "stopauctionat3 f=
the_elem ((%t. (if (f t=f (t+(1::nat))) then True else False))-`{True})"

definition stopauctionat where "stopauctionat l = 
filterpositions2 (%x. (x=True)) (sametomyleft' l)"
(* MC: I reuse what introduced to calculate argmax *)
abbreviation "stopauctionat' l == 
filterpositions2 (%x. (x=True)) (sametomyleft'' l)"
definition "stopat B = Min (\<Inter> {set (stopauctionat (unzip2 (B,,i)))| i::nat. i \<in> Domain B})" 
definition "stops B = \<Inter> {set (stopauctionat' (unzip2 (B,,i)))| i. i \<in> Domain B}"
abbreviation "stops' B == \<Inter> {(set o stopauctionat' o unzip2) (B,,i)| i. i \<in> Domain B}"
abbreviation "duration B == Max (size ` (Range B))"
(* abbreviation "livelinessList B == True # list_update (replicate (duration B) True) (stopat B) False" *)
abbreviation "mbc0 B == update2 (replicate (duration B) True) (stops B) (%x. False)"
(* yields a list returning for each instant the termination flag *)
definition "livelinessList B = True # update2 (replicate (duration B) True) (stops B) (%x. False)"
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
"amendedbid (b::dynbid) 0 = (b!0)" |
"amendedbid b (Suc t) = 
(liveliness' (amendedbid b t) (b!(Suc t)), lastvalidbid (amendedbid b t) (b!(Suc t)))"

fun amendedbidlist where (*MC: this assumes that the list of bids grows on the left through time *)
"amendedbidlist [] = [(True, 0::nat)]" |
"amendedbidlist (x # b) = 
(liveliness' ((amendedbidlist b)!0) x, lastvalidbid ((amendedbidlist b)!0) x) # (amendedbidlist b)"

abbreviation "amendedbidlist2 b == rev (amendedbidlist (rev b))"

abbreviation "amendedbids (B::dynbids) == B O (graph (Range B) amendedbidlist2)"

(*abbreviation "bidsattime B t == (snd o (%x. x!t))`(Range B)"*)
abbreviation "bidsattime B (t::nat) == B O (graph (Range B) (%x::((bool\<times>nat) list). snd (x!t)))"
definition "winner B = argmax (toFunction (bidsattime (amendedbids B) (stopat (amendedbids B))))
(Domain (bidsattime (amendedbids B) (stopat (amendedbids B))))"

value "amendedbids example03"
value "bidsattime (amendedbids example03) (stopat example03)"
value "amendedbids example03 O (graph (Range (amendedbids example03)) (%x. snd (x!6)))"
value "stopat (amendedbids example03)"
value "snd (nth (amendedbids example03,,20) 6)"
value "(% x. x!6)` ( Range (amendedbids example03))"
value "bidsattime (amendedbids example03) (stopat (amendedbids example03))"
value "stopat (amendedbids MMMM)"

(* MC: Not employed at the moment, could be used to model feedback to bidders 
for them to decide future bids based on how the auction's going *)
fun bid ::"('a list => 'a) => 'a list => 'a list"  where
"bid feedback []=[]" | "bid feedback (x#b) = (feedback (x#b))#b"

definition swap where "swap d = (% i. (%t. d t i))" 

abbreviation interface where "interface c == (nth (zip [t<0. t <- c] c))"

(*
abbreviation lastrounds where "lastrounds B == graph {1,2,3} (% i. 
set (stopauctionat ((map snd) (tolist 10 (amendedbid (B i))))))"

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

end

