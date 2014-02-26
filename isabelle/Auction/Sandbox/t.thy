theory t
imports Main "../Maximum"
"~~/src/HOL/Library/Code_Target_Nat"
"../RelationProperties"
Fun

begin
type_synonym instant=nat (*CR: defining instant in case later want to change instant type*)
type_synonym participant=nat
type_synonym price=nat
type_synonym newbid="instant => (bool \<times> price)"
type_synonym bids="instant => (participant => price)"

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

definition stopauctionat2 where "stopauctionat2 f=Min (Domain ((graph UNIV (%t. f (t+1::nat))) \<inter> 
(graph UNIV f)))"

definition stopauctionat3 where "stopauctionat3 f=
the_elem ((%t. (if (f t=f (t+(1::nat))) then True else False))-`{True})"

term "%x. (if (x=1) then True else False)"

term stopauctionat2
term "(%x::nat. (if (x=1) then 2 else 3))"
term "stopauctionat3 (%x::nat. (if (x=1) then (2::nat) else (3::nat)))"

(* CR: cur, prev implicitly defined; thus, they apply to any fixed number of bidders *)
definition flag where "flag prev cur = (if 
((snd cur) < (snd prev) \<or> \<not> (fst cur)) 
then False else True)"

definition lastvalidbid where 
"lastvalidbid prev cur = (if flag prev cur then (snd cur) else (snd prev))"

fun amendedbid where
"amendedbid b 0 = (b 0)" |
"amendedbid b (Suc t) = 
(flag (amendedbid b t) (b (Suc t)), lastvalidbid (amendedbid b t) (b (Suc t)))"

definition swap where "swap d = (% i. (%t. d t i))" 

abbreviation interface where "interface c == (nth (zip [t<0. t <- c] c))"

abbreviation tolist where "tolist N (f::(nat => 'a)) == [ (f i). i <- [0 ..< (Suc N)]]"

value "tolist (3::nat) (%x::nat. (if (x=1) then (2::nat) else 3))"

term amendedbid
abbreviation lastrounds where "lastrounds B == graph {1,2,3} (% i. 
set (stopauctionat ((map snd) (tolist 10 (amendedbid (B i))))))"

abbreviation example where 
"example == %t::instant. (if (t=0) then (True, 10::nat) else (True, 1))"

abbreviation lastround where "lastround B == Min (\<Inter> (Range  (lastrounds B)))"

abbreviation Example where "Example == (%i. example)"

value "lastround Example"

value "%i. (Example i (lastround Example))"

term "%i. ((map snd) (B i))"
value "stopauctionat [1,2,3::nat,2,2,3,4,5,5]"

term interface
value amendedbid
value "amendedbid (interface B)"
value "(%t::instant. (if (t=0) then 0 else 1))"

value "amendedbid example (1::instant)"
find_consts "'a list => (nat => 'a)"
end

