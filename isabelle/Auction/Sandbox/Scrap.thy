(* abbreviation "sublistAccordingTo list boolList == sublist list (set (filterpositions2 (%x. x=True) boolList))"

fun valid where "valid step [] = []" |
"valid step (x#xs) = (
(card((set (maxpositions (sublistAccordingTo xs (valid step xs))))) \<ge> 2 & (x=Max (set 
(sublistAccordingTo xs (valid step xs))))) \<or>
(card((set (maxpositions (sublistAccordingTo xs (valid step xs))))) = 1 & (x\<ge>Max (set 
(sublistAccordingTo xs (valid step xs))) + step))\<or>(xs = [] & (x \<ge> 0)))#(valid step xs)"

abbreviation "isGrowing step l == (\<forall>n\<in>{0..<size l}. l!(Suc n) - (l!n)\<ge>step)"
abbreviation "setOfAllowedBids step l == {x. x=Max (set l) \<or> (isGrowing step l \<and> x \<ge> step+Max (set l))}"

value "listToBidMatrix E01"
value "sameToMyLeft [1]"
lemma assumes "i\<in>set (stopAuctionAt l)" shows 
"l!i = l!(i-(1))" using assms stopAuctionAt_def filterpositions2_def sorry
lemma "set (stopAuctionAt l) = {Suc i| i. i\<in>{0..<size l}  & l!(Suc i) = l!i}"
unfolding filterPositionEquivalence sorry 
*)

