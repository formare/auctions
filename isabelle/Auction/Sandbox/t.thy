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
type_synonym submission="bool \<times> price"
type_synonym dynbid="submission list"
type_synonym dynbids="(instant \<times> dynbid) set"

abbreviation "unzip1 == map fst"
abbreviation "unzip2 == map snd"

(*MC: first basic approach. We have bids for each (natural) instant, from which we calculate, at a given instant,
a pair (boolean, lastvalidprice).
The first is a flag liveliness saying whether that bidder is still into play, and can be freely set by the bidder himself.
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

definition "stopat B = Min (\<Inter> {set (stopauctionat (unzip2 (B,,i)))| i. i \<in> Domain B})"

(* value "stopat {(10,[1,2,3,4::nat,4,4::nat]), (20::nat,[1,2,3,5,5,5::nat])}" *)

abbreviation "example02 == {
(10::nat, zip (replicate (10::nat) True) 
[1::nat,6,4,1,2,2,2]),
(20, zip (replicate (10::nat) True) 
[5::nat,4,7,7,8,3,3,3])
}"

value "stopat example02"

(* CR: cur, prev implicitly defined; thus, they apply to any fixed number of bidders *)
definition liveliness where "liveliness prev cur = (if 
((snd cur) < (snd prev) \<or> \<not> (fst cur)) 
then False else True)"

definition lastvalidbid where 
"lastvalidbid prev cur = (if liveliness prev cur then (snd cur) else (snd prev))"

fun amendedbid where
"amendedbid (b::dynbid) 0 = (b!0)" |
"amendedbid b (Suc t) = 
(liveliness (amendedbid b t) (b!(Suc t)), lastvalidbid (amendedbid b t) (b!(Suc t)))"

fun amendedbidlist where (*MC: this assumes that the list of bids grows on the left through time *)
"amendedbidlist [] = [(True, 0::nat)]" |
"amendedbidlist (x # b) = 
(liveliness (last (amendedbidlist b)) x, lastvalidbid (last (amendedbidlist b)) x) # (amendedbidlist b)"

abbreviation "amendedbids (B::dynbids) == B O (graph (Range B) amendedbidlist)"

term example02
value "stopat (amendedbids example02)"

(* MC: Not employed at the moment, could be used to model feedback to bidders 
for them to decide future bids based on how the auction's going *)
fun bid ::"('a list => 'a) => 'a list => 'a list"  where
"bid feedback []=[]" | "bid feedback (x#b) = (feedback (x#b))#b"

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

