theory t
imports Main "../Maximum"
"~~/src/HOL/Library/Code_Target_Nat"

begin
type_synonym instant=nat

(*MC: first basic approach. We have bids for each (natural) instant, from which we calculate, at a given instant,
a pair (boolean, lastvalidprice).
The first is a flag saying whether that bidder is still into play, and can be freely set by the bidder himself.
But it also turn into false if the bid is invalid (which for the moment just coincides with the fact that his bid has decreased, 
but can be enriched with other conditions, like reserve price, minimal increase, etc...).
The second preserves the last valid bid, which for the moment coincides with the price of last time we computed a true flag. *)

definition sametomyleft where 
"sametomyleft l = [fst x = snd x. x <- zip l (((hd l) + 1)# l)]"

definition sametomyright where 
"sametomyright l = [fst x = snd x. x <- zip l (drop 1 l)]"

definition stopauctionat where "stopauctionat l = 
filterpositions2 (%x. (x=True)) (sametomyleft l)"
(* MC: I reuse what introduced to calculate argmax *)

definition flag where "flag prev cur = (if 
((snd cur) < (snd prev) \<or> \<not> (fst cur)) 
then False else True)"

definition lastvalidbid where 
"lastvalidbid prev cur = (if flag prev cur then (snd cur) else (snd prev))"

fun amendedbid where
"amendedbid b 0 = (b 0)" 
|
"amendedbid b (Suc n) = 
(flag (amendedbid b n) (b (Suc n)), lastvalidbid (amendedbid b n) (b (Suc n)))"

value "(%n::nat. (if (n=0) then 0 else 1))"

abbreviation example where 
"example == %n::nat. (if (n=0) then (True, 10::nat) else (True, 1))"

value "amendedbid example (1::nat)"

end

