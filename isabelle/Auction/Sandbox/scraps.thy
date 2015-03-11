theory scraps

imports Main

begin

lemma assumes "a\<in>allAllocations' N G" "n \<noteq> addedBidder N" "addedBidder N \<notin> Domain a" shows True
proof -
have "Range a \<subseteq> Pow G" sorry
let ?A=allAllocations' let ?AA=allStrictAllocations'''
let ?N="N"
let ?i="addedBidder ?N" 
let ?NN="?N \<union> {?i}"
let ?g="G-\<Union>(Range a)"
let ?a="a \<union> {(?i, ?g)}" let ?G_="\<Union>Range ?a"
have "\<Union>(Range a) \<subseteq> G" sorry then 
have "?G_ \<subseteq> G" by simp
have "a \<in> ?A ?N G" sorry 
then have "?a \<in> ?AA ?NN ?G_" sorry 
then have "?a -- n \<in> ?AA (?NN - {n}) (?G_ - \<Union>(?a``{n}))" by (rule nn31)
moreover have "... = ?AA (?N - {n} \<union> {?i}) (?G_-\<Union>(?a``{n}))" using assms(2) by auto
moreover have "addedBidder (?N-{n}) = ?i" sorry
ultimately have "?a -- n \<in> ?AA (?N-{n} \<union> {addedBidder(?N-{n})}) (?G_-\<Union>(?a``{n}))" by auto
then have "(Outside' {addedBidder(?N-{n})}) (?a -- n) \<in> 
(Outside' {addedBidder(?N-{n})}) `(?AA (?N-{n} \<union> {addedBidder(?N-{n})}) (?G_-\<Union>(?a``{n})))" 
by simp
moreover have "... = ?A (?N-{n}) (?G_-\<Union>(?a``{n}))" by (metis nn24)
ultimately have "(?a -- n) -- ?i \<in> ?A (?N-{n}) (?G_-\<Union>(?a``{n}))" by simp
moreover have "(?a -- n) -- ?i = (?a -- ?i) -- n" using assms 
by (metis (hide_lams, no_types) Un_insert_left Un_insert_right insert_commute ll52)
moreover have "?a -- ?i = a" using assms Outside_def by auto
ultimately have "a -- n \<in> ?A (?N-{n}) (?G_-\<Union>(?a``{n}))" by simp
moreover have "... \<subseteq> ?A (?N-{n}) ?G_" using assms nn33 nn28d DiffE subsetI 
sorry
show ?thesis sorry
qed

lemma assumes "a \<in> allStrictAllocations' N G" shows "Domain a \<subseteq> (N \<union> {addedBidder N})" using assms by blast
lemma assumes "a \<in> allStrictAllocations' N G" shows "\<Union> (Range a) = G" 
using assms all_partitions_def is_partition_of_def by (metis (lifting) Int_Collect mem_Collect_eq)

lemma assumes "a \<in> allAllocations' N G" shows
"a outside {n, addedBidder N} \<in> (Outside' {addedBidder (N-{n})})`(allAllocations' (N-{n}) G)"
using assms Outside_def nn22 lm19b lm35 
proof -
let ?n="{addedBidder (N-{n})}" let ?N="{n, addedBidder N}" let ?U=strictAllocationsUniverse
have "a outside ?N \<in> ?U" using assms nn22 Outside_def lm35 
proof -
  have "\<And>u. u \<in> allAllocations' N G \<longrightarrow> u \<in> allAllocations"
    using nn22 by auto
  hence "a \<in> allAllocations"
    using assms by simp
  hence "a - {n, addedBidder N} \<times> Range a \<in> allAllocations"
    using lm35 by auto
  thus "a -| {n, addedBidder N} \<in> allAllocations"
    by (metis Outside_def)
qed
have "Domain (a outside ?N) \<subseteq> N - ?N " using assms nn22 Outside_def sorry 
show ?thesis sorry
qed

lemma assumes "n \<in> Partipants b'" shows 
"(Outside' {n, addedBidder' b'}) ` (maximalAllocations''' G b') \<subseteq> 
(Outside' {addedBidder (Participants b' - {n})}) ` allAllocations' (Participants b' - {n}) G"
using assms Outside_def nn21 sorry
abbreviation "vcgp''' N \<Omega> b random n ==
(Max (setsum b ` (singleoutside' (addedBidder N))`(allAllocations' (N-{n}) (set \<Omega>)))) - 
(setsum b (vcga'' N \<Omega> b random -- n))"

lemma "alpha' N G b n = alpha (N\<union>{auctioneer}) G (toFullBid G b) (n::participant)" by fast
lemma "alpha' N G b n = Max ((setsum (toFullBid G b))`(possibleAllocationsRel ((N\<union>{auctioneer})-{n}) G))"
by fast

lemma assumes "a \<in> allStrictAllocations' N G" shows
"a -- n \<in> allStrictAllocations' (N-{n}) (G - (a,,n))" sorry

lemma assumes "card N > 0" "distinct G" "G \<noteq> []" shows 
"winningAllocationsRel N (set G) bids \<inter> possibleAllocationsAlg2 N G \<noteq> {}"
using assms lm70b lm03 sorry

lemma "chosenAllocation N G bids random \<in> winningAllocationsRel N (set G) bids" 
using assms mm83 mm84b sorry


lemma assumes "distinct G" shows 
"possibleAllocationsAlg N (set G) = possibleAllocationsAlg3 N G" (is "?L=?R") 
using assms possible_allocations_alg_def injections_equiv all_partitions_paper_equiv_alg 
proof -
let ?i=injections_alg let ?p=all_partitions_alg let ?G="set G" 
let ?P=all_partitions_list
have "?R= map converse (concat [?i Y N. Y <- ?P G ])" by fast
have "set (?p ?G) \<subseteq> set (?P G)" using assms mm90 all_partitions_paper_equiv_alg sorry
have "?L = map converse (concat [?i Y N. Y <- ?p ?G ])" by simp
moreover have " ... = ?R" sorry
show ?thesis sorry
qed

lemma assumes "distinct G" shows 
"set (possibleAllocationsAlg N (set G)) \<supseteq> possibleAllocationsAlg2 N G" 
using assms possible_allocations_alg_def injections_equiv all_partitions_paper_equiv_alg 
sorry

corollary assumes "True" shows 
"takeAll (%x. x\<in>(winningAllocationsRel N (set G) bids)) (possibleAllocationsAlg N (set G)) \<noteq> []"
using mm84b
proof -
let ?w=winningAllocationsRel let ?P=possibleAllocationsAlg2 let ?p=possibleAllocationsRel
let ?G="set G"
(*
let ?l="?P N ?G" let ?P="%x. x \<in> ?w N ?G bids" 

have "{} \<noteq> ?w N ?G bids " sorry
have "card N > 0 & distinct G" sorry
moreover have "set ?l = ?p N ?G" using lm70b sorry  
then have "?P -` {True} \<noteq> {}" by blast
*)
show ?thesis sorry
qed


lemma assumes "(a outside {i}) \<union> ({i}\<times>X) \<in> allStrictAllocations' N G" 
shows "a outside {i} \<in> allAllocations' (N-{i}) G" using assms nn28 Outside_def paste_def sorry

lemma assumes "a \<in> allAllocations' N G" "G-\<Union> Range a \<noteq> {}" shows 
"(a \<union> {(addedBidder N,G-\<Union> Range a)} \<in> allStrictAllocations''' (N\<union>{addedBidder N}) G)"
using assms Outside_def paste_def nn28 sorry

lemma nn31: assumes "a \<in> allStrictAllocations''' N G" shows 
"a outside X \<in> allStrictAllocations''' (N-X) (G-\<Union>(a``X))"
using assms lm43 possible_allocations_rel_def nn28 lm43b nn28b lm35c nn30 Outside_def sorry

lemma assumes "i \<notin> (Domain a)" "a \<in> allAllocations" "Y \<inter> \<Union> Range a = {}" "Y\<noteq>{}" shows 
"a \<union> ({(x,Y)}-{(x,{})}) \<in> allAllocations" using assms lm23 nn39 lm36b sorry


corollary lm43e: assumes "a \<in> allAllocations" shows 
"(a outside ({n,z} \<union> {z'})) \<union> {z'}\<times>({\<Union> (a``({n,z}\<union>{z'}))} - {{}}) \<in> allAllocations"
using assms by (rule lm43d) 
lemma nn25: "Domain ((R outside (X \<union> {i})) \<union> ({i} \<times> Y)) \<subseteq> Domain R - X \<union> {i}" using assms Outside_def 
by auto
corollary nn26: assumes "a \<in> possibleAllocationsRel N G" shows 
"Domain ((a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}}))) \<subseteq> (N-X) \<union> {i}" (is "?L \<subseteq> ?R") using assms nn24
lm43b nn24c Outside_def nn25 
proof -
have "?L \<subseteq> Domain a - X \<union> {i}" using nn25 assms by metis 
moreover have "... \<subseteq> ?R" using assms nn24c sorry
ultimately show ?thesis by blast
qed
corollary nn26b:  assumes "a \<in> possibleAllocationsRel N G" shows 
"(a outside (X\<union>{i})) \<union> ({i}\<times>({\<Union>(a``(X\<union>{i}))}-{{}})) \<in> possibleAllocationsRel ((N-X) \<union> {i}) G" (is "?L \<in> ?R")
proof -
let ?A=allAllocations have "a \<in> ?A" using nn24c assms by (metis (lifting, mono_tags))
then have "?L \<in> ?A & \<Union> Range ?L = \<Union> Range a" by (rule lm43b)
moreover have "Domain ?L \<subseteq> (N-X) \<union> {i}" using assms nn26 by metis 
ultimately show ?thesis using assms nn24c by (metis (lifting, mono_tags))
qed


corollary nn26g: assumes "a \<in> possibleAllocationsRel N G" shows 
"(a outside ({n,i}\<union>{i})) \<union> ({i}\<times>({\<Union>(a``({n,i}\<union>{i}))}-{{}})) \<in> possibleAllocationsRel ((N-{n,i}) \<union> {i}) G" (is "?L \<in> ?R")
using assms by (rule nn26b)

corollary nn26h: assumes "a \<in> possibleAllocationsRel N G" shows 
"(a outside {n,i}) \<union> ({i}\<times>({\<Union>(a``{n,i})}-{{}})) \<in> possibleAllocationsRel ((N-{n,i}) \<union> {i}) G" 
proof - have "{n,i}\<union>{i}={n,i}" by fast thus ?thesis using assms nn26g by metis qed

corollary nn26i: assumes "a \<in> allStrictAllocations' N G" "n \<noteq> i" shows 
"(a outside {n,i}) \<union> ({i}\<times>({\<Union>(a``{n,i})}-{{}})) \<in> possibleAllocationsRel ((N-{n}) \<union> {i}) G"
proof - have "N-{n,i}\<union>{i}=N-{n}\<union>{i}" using assms(2) by fast thus ?thesis using assms(1) nn26h by metis qed

lemma assumes "(a -- i) \<union> ({i}\<times>X) \<in> allAllocations" 
shows "a -- i \<in> allAllocations" using assms nn28 Outside_def paste_def lm35b outside_union_restrict by (smt Un_commute Un_upper2)

corollary nn26c: assumes "a \<in> possibleAllocationsRel (N \<union> {addedBidder N}) G" shows
"(a outside ({n, addedBidder N}\<union>{addedBidder (N-{n})})) \<union> ({addedBidder (N-{n})}\<times>({\<Union>(a``({n, addedBidder N} \<union> {addedBidder (N-{n})}))} - {{}}))
\<in> possibleAllocationsRel (((N \<union> {addedBidder N})-{n, addedBidder N}) \<union> {addedBidder (N-{n})}) G" using assms by (rule nn26b)


lemma nn26d: assumes "N=int`(NN::participant set)" "a \<in> possibleAllocationsRel (N \<union> {addedBidder N}) G" shows
"(a outside ({n, addedBidder N, addedBidder (N-{n})})) \<union> 
({addedBidder (N-{n})}\<times>({\<Union>(a``({n, addedBidder N} \<union> {addedBidder (N-{n})}))} - {{}}))
\<in> possibleAllocationsRel ((N - {n}) \<union> {addedBidder (N-{n})}) G" (is "?L \<in> _") using assms nn26c nn27c
proof - let ?b2="addedBidder N" let ?b1="addedBidder (N-{n})"
have "?L \<in> possibleAllocationsRel(N\<union>{?b2}-{n, ?b2}\<union>{?b1}) G" using assms nn26c sorry
moreover have "N \<union> {?b2} - {n, ?b2} = N - {n}" using assms nn27c by blast ultimately show ?thesis by fastforce
qed

corollary nn26f: assumes "N=int`(NN::participant set)" "f=addedBidder" "f N = f (N-{n})"
"a \<in> possibleAllocationsRel (N \<union> {f N}) G" shows
"(a outside {n, f N}) \<union> ({f (N-{n})}\<times>({\<Union>(a``({n, f N}))}-{{}})) \<in> 
possibleAllocationsRel ((N-{n})\<union>{f (N-{n})}) G" using assms nn26d sorry

corollary nn27b: assumes "finite N" shows "addedBidder N \<notin> N" using assms nn27 sorry

corollary nn26e: assumes "finite N" "a \<in> possibleAllocationsRel (N \<union> {addedBidder N}) G" shows
"(a outside ({n, addedBidder N}\<union>{addedBidder (N-{n})})) \<union> ({addedBidder (N-{n})}\<times>({\<Union>(a``({n, addedBidder N} \<union> {addedBidder (N-{n})}))} - {{}}))
\<in> possibleAllocationsRel ((N - {n}) \<union> {addedBidder (N-{n})}) G" (is "?L \<in> ?R") using assms nn26c nn27b 
proof -
let ?b2="addedBidder N" let ?b1="addedBidder (N-{n})"
have "?L \<in> possibleAllocationsRel (N \<union> {?b2} - {n, ?b2} \<union> {?b1}) G" using assms nn26c by metis
moreover have "N \<union> {?b2} - {n, ?b2} = N - {n}" using assms nn27b by blast
ultimately show ?thesis by fastforce
qed


corollary nn22: "(a \<in> allStrictAllocations' N G) = 
(a \<in> allAllocations & Domain a \<subseteq> N & \<Union> (Range a) = G)" sorry


lemma assumes "a \<in> possibleAllocationsRel N G" "finite G" shows "setsum (maxbid a N G) a = card G"
using assms sorry







































lemma assumes "\<forall>x. x \<in> X \<longrightarrow> finite (snd x)" "finite X" 
"is_partition (snd ` X)" shows 
"setsum (card \<circ> snd) X = card (\<Union> (snd ` X))" using assms sorry

lemma assumes "allocation \<in> allAllocations" shows
"is_partition (omega ` allocation)" using assms is_partition_def sorry

lemma assumes "finite G" "finite N" "a \<in> possibleAllocationsRel N G" shows 
"card (pseudoAllocation a) = card G" 
using assms possible_allocations_rel_def injections_def all_partitions_def sorry

lemma assumes "finite a" "\<forall>x \<in> a. finite (snd x)" shows "finite (pseudoAllocation a)" 
using assms sorry

lemma "pseudoAllocation a \<subseteq> (Domain a \<times> (finestpart (\<Union> Range a)))" 
using assms finestpart_def sorry

lemma assumes "!x. x \<in> Range a \<longrightarrow> finite x" "is_partition (Range a)" shows 
"card (pseudoAllocation a) = card (\<Union> Range a)"
using assms is_partition_def mm26 sorry


lemma mm08: assumes "finite X" shows 
"setsum f X <= card X * Max (Range (graph X f)) & 
setsum f X <= card X * Max (Range (graph X f))" using assms graph_def sorry

lemma mm09: assumes "finite a" "finite N" "finite G" shows 
"Min (Range (bidMaximizedBy a N G || a)) >= 1 &
Max (Range (bidMaximizedBy a N G || a)) <= 1" using assms Range_def paste_def
sorry

lemma assumes "runiq f" shows "Graph (toFunction f) \<supseteq> f" using assms Graph_def toFunction_def 
runiq_def sorry

lemma "setsum f X = setsum f (X - (f -` {0}))" using assms sorry

lemma assumes "finite aa" shows "proceeds (toFunction (bidMaximizedBy aa N G)) a = 
proceeds (toFunction (bidMaximizedBy aa N G)) (a \<inter> aa)"
using assms mm10 mm09 mm08 sorry

lemma assumes "finite a1" "runiq (a1^-1)" "\<Union> (snd ` a1) = G" "Domain a1=N" shows 
"proceeds (toFunction (bidMaximizedBy a1 N G)) a1 = card a1 * Max (Range ((bidMaximizedBy a1 N G)))"
using assms runiq_def mm08 mm09 mm10 sorry

lemma assumes "runiq (a2^-1)" "runiq (a1^-1)" "\<Union> (snd ` a1) = G" "\<Union> (snd ` a2) = G" shows 
"proceeds (toFunction (bidMaximizedBy a1 N G)) a2 >= card G"
using assms runiq_def sorry


lemma assumes "card X > 0" "finite X" "\<forall> n. card (prova f X (n+1)) < card (prova f X n)" 
shows "\<forall>m. EX n. card (prova f X n)<=1"
using assms prova_def sorry

abbreviation "pred5 (m::nat) == \<forall>f. ((f (0::nat)=m & (\<forall>n. (f n - 1 >= f (Suc n)))) \<longrightarrow> (f (f 0))<=(0::nat))"

lemma mm00: "pred5 (0::nat)" by fastforce

lemma mm01: assumes "pred5 m" shows "pred5 (Suc m)"
proof -
{ 
  fix f::"nat => nat" let ?g="%n. f n - 1"   
  {
    assume 
    3: "f (Suc m) > 0" assume 
    2: "(f (0::nat)=Suc m & (\<forall>n. (f n - 1 >= f (Suc n))))"     
    then moreover have "\<forall>n. (?g n - 1 >= ?g (Suc n))" by (metis diff_le_mono)
    ultimately have "?g 0=m & (\<forall>n. (?g n - 1 >= ?g (Suc n)))" by force then have 
    5: "?g (?g 0) \<le> 0" using assms by auto
    moreover have "f m > f(f 0)" using 3 2 by smt
    ultimately have "f (?g 0) - 1 \<ge> f (f 0)" using 2 by auto
    then have "?g (?g 0) \<ge> f (f 0)" by fast
    then have "f (f 0) \<le> 0" using 5 by simp
  }  
}
then show ?thesis using assms by (metis le_less_linear)
qed

lemma mm01b: "\<forall>k::nat. (pred5 k \<longrightarrow> pred5 (Suc k))" using mm01 by fast

lemma mm02: "\<forall>m::nat. pred5 m" using assms mm00 mm01b lll20 nat_induct 
proof -
{
    fix P::"nat => bool" assume 
    23: "P=pred5"
    then have "P (0::nat) & (!k::nat. (P k \<longrightarrow> P (Suc k)))" 
    using mm00 mm01b by fast
    then have "!n::nat. (P n)" using nat_induct by auto
}
thus ?thesis by presburger
qed

lemma mm02b: assumes "\<forall>n. (f n - 1 >= f (Suc n))" shows "f (f 0)<=(0::nat)" using mm02 assms by blast



lemma mm03: assumes "\<forall>X. f (n+1) X <~ X" shows 
"geniter f (n+1) X <~ geniter f n X" using assms geniter_def 
proof -
let ?g=geniter
have "?g f (n+1) X = f (n+1) (?g f n X)" using geniter_def by simp
moreover have "f (n+1) (?g f n X) <~ ?g f n X" using assms by fast
ultimately show "?g f (n+1) X <~ ?g f n X" by simp 
then have "card (?g f (n+1) X) - 1 \<le> card (?g f n X) - 2" by fast
let ?h="%n. card (?g f n X) - 1"
qed

lemma mm04: assumes "\<forall>n. \<forall>X. f (n+1) X <~ X" shows "\<forall>n. geniter f (n+1) X <~ geniter f n X" using assms mm03 by blast

lemma mm05: assumes "\<forall>n. \<forall>X. f (n+1) X <~ X" shows "card (geniter f (card (geniter f 0 X) - 1) X) - 1 <= 0" 
proof -
let ?g=geniter let ?h="%n. card (?g f n X) - 1"
have "\<forall>n. ?h (Suc n) <= ?h n - 1" using assms by (metis Suc_1 Suc_eq_plus1 diff_diff_left mm03)
thus ?thesis by (rule mm02b)
qed

lemma mm06: assumes "X <~ Y" "Y <~ Z" shows "X <~ Z" using assms by linarith

lemma assumes "finite Y" "X \<subseteq> Y" shows "card X - 1\<le> card Y - 1" using assms 
by (metis card_mono diff_le_mono)

lemma mm07: assumes "finite Y" "X \<subseteq> Y" "Y <~ Z" shows "X <~ Z" using assms card_mono diff_le_mono 
by (metis le_trans)

lemma mm07b: assumes "finite Z" "X <~ Y" "Y \<subseteq> Z" shows "X <~ Z" using assms card_mono diff_le_mono 
by (metis le_trans)



lemma assumes "distinct list" shows "perm (permL list n) list" 
using assms permL_def sorry

corollary assumes "takeAll P list \<noteq> []" shows "set (takeAll P list) \<subseteq> set list"
using assms set_def mm98 filterpositions2_def sorry

lemma "sublist l {0..<1+n} @ (sublist l {1+n..<1+n+m}) = sublist l {0..<1+n+m}" 
using sublist_append sorry
lemma "set (sublist l {0..<1+(n::nat)}) \<union> 
set (sublist l {1+n..<1+size l}) = set (sublist l ({0..<1+(n::nat)}\<union>{0..<1+size l}))" sorry

lemma assumes "l \<noteq> []" shows "(nth l) -` (set l) \<subseteq> {0..<1+size l}" using assms sorry


























(*

corollary mm92b: assumes "finite G" "finite N"  shows 
"(((arg_max' \<circ> setsum) (resolvingBid N G bids random))
\<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N G) 
= {chosenAllocation N G bids random}" using assms mm92 mm93 
by simp

corollary mm92c: assumes "finite G" "finite N"  shows 
"card ((((arg_max' \<circ> setsum) (resolvingBid N G bids random))
\<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N G)) 
= 1" using assms mm92b by auto

abbreviation "Tiebids N G bids random == tiebids (chosenAllocation N G bids random) N G"

corollary assumes "finite G" "finite N"  shows 
"card ((((arg_max' \<circ> setsum) (Tiebids N G bids random)) \<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N G)) 
= 1" using assms mm92c by fast

lemma "(arg_max' \<circ> setsum) bids (possibleAllocationsRel N G) = winningAllocationsRel N G bids"
by force

corollary assumes "finite G" "finite N" shows 
"card ((((arg_max' \<circ> setsum) (somebids)) \<circ> ((arg_max' \<circ> setsum) bids)) (possibleAllocationsRel N G)) 
= 1" using assms mm92c sorry

(* tiebids (chosenAllocation N G bids random) N G *)

abbreviation "terminatingAuctionAlg N G bids random == argmax 
(proceeds (tiebids (hd (permL 
(takeAll (%x. x \<in> set (argmax (proceeds bids) (possibleAllocationsAlg3 N G))) (possibleAllocationsAlg3 N G)) 
(random::nat))) N (set G)))
(argmax (proceeds bids) (possibleAllocationsAlg3 N G))"


term "terminatingAuction N00 (set G00)"
value "arg_max' (%x. 1/x) {1,2::nat}"
value "possibleAllocationsAlg N00 (set G00)"
value "terminatingAuction N00 (set G00) (toFunction b00) 1"

abbreviation "indexof l x == hd (filterpositions2 (%y. x=y) l)"
notation indexof (infix "!-`" 75)
 
abbreviation "one N G random index == 
(% g n. (permL (sorted_list_of_set N) (random (index g))) !-` n + (card N)^(index g))"

abbreviation "tieBreakBidsSingle N G random index == % n g. 
(permL (sorted_list_of_set N) (random (index g))) !-` n + (card N)^(index g)" 
(* Gives, for each _single_ good, and each participant, a bid.
In such a way that the resulting proceeds are unique for each possible allocation
(as soon as index is injective)
*)

abbreviation "tieBreakBids N G random index == split (% n X.
setsum (tieBreakBidsSingle N G random index n) X
)"

value "proceeds (tieBreakBids {0::nat, 1} {10::nat,1} id id)"

abbreviation "tieBreaker N G random index == %X. arg_max' (proceeds (tieBreakBids N G random index))X "

lemma "!X. card (tieBreaker N G random index X) = 1" sorry

abbreviation "tieBreakerSeq N G random index == 
%n. (if (n=0) then (%X. tieBreaker N G random index X) else id)"

abbreviation "auction b t == geniter (%n. (t n) o (arg_max' (proceeds (b n))))" 
(* abbreviation "bidsequence b r == (%t. )" *)
(* abbreviation "auction B == geniter (%t. arg_max' (proceeds (B t)))" *)

lemma assumes "!n. !X. t n X <~ X" shows 
"card ((auction b t) 
(card (auction b t 0 X) - 1)
 X) - 1 <= 0" using mm05 assms 
proof -
let ?c=card let ?g=geniter let ?f="%n. (t n) o (arg_max' (proceeds (b n)))"
{
  fix n X
  have "arg_max' (proceeds (b n)) X \<subseteq> X" by auto
  moreover have "(t n) (arg_max' (proceeds (b n)) X) <~ arg_max' (proceeds (b n)) X" 
  using assms by fast
  moreover have "finite X" sorry
  ultimately
  have "((t n) o (arg_max' (proceeds (b n)))) X <~ X" using mm07b by auto
}
then have "\<forall>n. \<forall>X. ?f (n+1) X <~ X" by blast
then have "?c (?g ?f (?c (?g ?f 0 X) - 1) X) - 1 <= 0" using mm05 by fast
moreover have "auction b t=?g ?f" by fast
ultimately have "?c (auction b t (?c (auction b t 0 X) - 1) X) - 1 <= 0" by fast
then show ?thesis by fast
qed

lemma assumes "finite N" "finite G" 
(* "f 0=arg_max' (proceeds (b 0))" *) 
(* This only settles wdp, leaving the price determination completely undetermined *)
"!n. f (Suc n) = (%X. arg_max' (proceeds (b n)) (g (f n X)))"
"\<forall>Y. card (g Y) - 1 <= card Y - 2" shows
"EX n. card (prova f (possibleAllocationsRel N G) n) <= 0"
using assms prova_def prova_def mm02b sorry

notepad
begin
fix f N G fix n::nat fix b g
let ?X="possibleAllocationsRel N G"
have "prova f (possibleAllocationsRel N G) (n+2) = f (n+1) (prova f (possibleAllocationsRel N G) (n+1))"
using prova_def by auto
moreover have "... = arg_max' (proceeds (b n)) (g (f n ?X))" sorry
moreover have "g (f n ?X) \<subseteq> f n ?X" sorry
ultimately have "prova f ?X (n+2) \<subseteq> arg_max' (proceeds (b n)) (f n ?X)" sorry
end

lemma fixes f::"nat => nat" 
assumes "f 0 = m" "\<forall>n. (f n) - 1 >= f (n+1)" shows "f m <= 0" 
using assms nat_less_induct measure_induct_rule full_nat_induct infinite_descent nat_induct
lll20 sorry

lemma fixes f::"nat => nat" 
assumes "\<forall>n. ((f n) - 1 >= f (n+1) & f n > (0::nat))" shows "f ((f 0)+1) <= 2"
using assms infinite_descent sorry

lemma assumes "\<forall>(n::nat). (f n) - 1 >= f (n + (g n))" shows "EX n. f n = (0::nat)" 
using assms infinite_descent nat_induct sorry
term "Random_Sequence.not_random_dseq"
value "fst (Random.next (1,1))"

value "Random.pick [(1::natural,10::nat),(2,12),(3,13)] 3"

term "Limited_Sequence.single"

value "Random_Sequence.single (1::nat)"

end

*)


(*
abbreviation "auctioneer == 0"
(* MC: restore previous definition, after changing condition1 *)
abbreviation "toPartialAllo a == a -- auctioneer"
term "winningAllocationsAlg N G "
(*abbreviation "seller == auctioneer"*)
(*MC: converters*)
(* abbreviation "toFullBid Goods (bids::altbids) == (({auctioneer} \<times> Pow (Goods)) :== (%x. (0::price))) bids" *)
abbreviation "toFullBid Goods bids == (({auctioneer} \<times> (Pow Goods)) :== (%x. 0)) bids"
abbreviation "vcgas' N G b == winningAllocationsRel (N \<union> {auctioneer}) G (toFullBid G b)"
abbreviation "Vcgas N G b == winningAllocationsAlg (N \<union> {auctioneer}) G (toFullBid (set G) b)"
abbreviation "vcga N G b t == toPartialAllo (t (vcgas' N G b))" 
abbreviation "vcga' N G bids random == the_elem 
(arg_max' (setsum (resolvingBid (N\<union>{auctioneer}) G (toFullBid (set G) bids) random))
(vcgas' N (set G) bids))"

lemma n12: "Range (toPartialAllo a) \<subseteq> Range a" by (metis Range_outside_sub subset_refl)

corollary nn12a: assumes "t (vcgas' N G b) \<in> vcgas' N G b" shows "is_partition (Range (vcga N G b t))"
using assms lm47 is_partition_of_def Range_outside_sub subset_refl by (smt in_mono lm03 subset_is_partition)

corollary nn12b: assumes "t (vcgas' N G b) \<in> vcgas' N G b" shows "Range (vcga N G b t) \<subseteq> Pow G"
using assms in_mono lm03 lm47 is_partition_of_def nn11 Range_outside_sub  by (metis (lifting, no_types))

corollary nn12: assumes "t (vcgas' N G b) \<in> vcgas' N G bcon" 
(*this is an assumption about t, not about b, G or N*)
shows "is_partition (Range (vcga N G b t)) & Range (vcga N G b t) \<subseteq> Pow G"
using assms nn12a nn12b by fast
*)


(* BIGSKIP
lemma "possibleAllocationsRel N G \<subseteq> allocationsUniverse" using assms possible_allocations_rel_def 
injections_def all_partitions_def is_partition_of_def lm24 lm25 lm25b lm26 
sorry

lemma assumes "X \<in> (strictCovers G)" shows "(\<Union> X) = G" sorry
lemma "all_partitions G = allPartitions \<inter> (strictCovers G)" sorry
lemma "possibleAllocationsRel N G \<subseteq> allocationsUniverse \<inter> ((Union \<circ> Range) -` {G}) \<inter> (Dom -` (Pow N))" 
using assms possible_allocations_rel_def sorry

lemma assumes "a1 \<in> possibleAllocationsRel N1 G1" "a2 \<in> possibleAllocationsRel N2 (G2-G1)"
shows "(a1 +* a2) \<in> possibleAllocationsRel (N1 \<union> N2) (G1 \<union> G2)" using assms 
possible_allocations_rel_def
proof -
let ?a="a1 +* a2" let ?u=runiq let ?d=Domain let ?r=Range let ?I=allInjections 
let ?N="N1 \<union> N2" let ?G="G1 \<union> G2" let ?P=all_partitions' let ?g2="G2-G1" have 
0: "?d a1 \<subseteq> N1 & ?d a2 \<subseteq> N2 & ?r a1 \<in> ?P G1 & ?r a2 \<in> ?P ?g2" using assms lm19 sorry
have "?u a1 & ?u (a1^-1)" using assms(1) possible_allocations_rel_def sorry
moreover
have "?u a2 & ?u (a2^-1)" using assms(1) possible_allocations_rel_def sorry
ultimately moreover have "?u ?a" by (metis runiq_paste2)
moreover have "?r a1 \<inter> (?r a2)={}" sorry
then moreover have "?u (?a^-1)" using runiq_converse_paste assms by (metis calculation(1) calculation(2) lll77b)
ultimately moreover have "?a \<in> ?I" by fast
moreover have "?d ?a \<subseteq> ?N" using assms paste_def 0 by (metis Un_mono paste_Domain)
moreover have "?r ?a \<subseteq> (?r a1) \<union> (?r a2)" by (metis paste_Range)
moreover have "is_partition (?r a1) & is_partition (?r a2)" sorry
then moreover have "is_partition ((?r a1) \<union> (?r a2))" using assms lm20 0 by (metis (lifting, mono_tags) Diff_disjoint mem_Collect_eq)
moreover have "is_partition (?r ?a)" using 0 assms is_partition_of_def
by (metis calculation(10) calculation(8) subset_is_partition)
moreover have "?r a1 \<inter> (?r a2)={}" by (metis calculation(4))
ultimately moreover have "?r ?a = (?r a1) \<union> (?r a2)" using paste_def lm21 assms 0 sorry
show ?thesis sorry
qed

lemma assumes "n \<notin> N" shows "Max ((proceeds b)`(possibleAllocationsRel (N-{n}) G)) = 
proceeds b (winningAllocationRel N G t b -- n)" using assms sorry

lemma lll74: assumes "a\<inverse> \<in> possible_allocations_rel G N" 
"Y2 \<inter> (G - a,,,x)={}"
"Y2 \<noteq> {}"
shows "(a +< (x,Y2))\<inverse> \<in> possible_allocations_rel (G-(a,,,x)\<union>Y2) (N \<union> {x})"
proof -
let ?Y1="a,,,x" let ?u=runiq let ?A=possible_allocations_rel let ?aa="a\<inverse>" let ?I=injections
let ?P=all_partitions let ?r=Range let ?a2="a +< (x, Y2)" let ?d=Domain
obtain pG where 
1: "?aa \<in> ?I pG N & pG \<in> ?P G" using assms(1) possible_allocations_rel_def by fastforce
have "?u a" using 1 injections_def
by (smt converse_converse mem_Collect_eq)
then have 
12: "?u (a +< (x,Y2))" using lll73 by metis
have "?r (a -- x)=a``(?d a - {x})" using Outside_def by blast
moreover have 
0: "?u ?aa & ?u a" using assms by (metis `runiq a` lll81) ultimately
have "?r (a -- x) \<inter> (a``{x}) = {}" using lll78 
by metis 
moreover have 
3: "(a -- x) \<union> {(x, Y2)} = ?a2" using paste_def 
by (metis Domain_empty Domain_insert fst_conv snd_conv)
have 
6: "?r ?a2 = ?r (a -- x) \<union> {Y2}" using 3 by auto
moreover have "?r a = ?r (a -- x) \<union> (a``{x})" using Outside_def
by blast
ultimately moreover have "?r (a -- x) = ?r a - a``{x}" by auto
moreover have "is_partition (?r a) & (\<Union> (?r a))=G" using 1 by (metis Domain_converse assms(1) is_partition_of_def lll81)
ultimately moreover have "a``{x} \<subseteq> ?r a" by (metis Un_upper2)
ultimately have 
5: "(?r (a -- x)) partitions (G - \<Union>(a``{x}))" using lll80 by metis
then have 
4: "\<Union> (?r (a -- x)) = (G - a,,,x)" unfolding is_partition_of_def by fast
then have "Y2 \<notin> (?r (a -- x))" using lll79 assms subsetI by metis
then have "?r {(x, Y2)} \<inter> ?r (a -- x) = {}" using assms by blast
moreover have "?u {(x, Y2)}" by (metis runiq_singleton_rel)
moreover have "(a--x)\<inverse> \<subseteq> ?aa" using Outside_def
by blast
moreover then  have "?u ((a -- x)\<inverse>)" using 0 subrel_runiq by metis
ultimately moreover have "?u (((a -- x) \<union> {(x, Y2)})\<inverse>)" using 0 by (metis 
IntI Range_insert empty_iff insert_iff runiq_conv_extend_singleton)
ultimately have 
11: "?u (?a2\<inverse>)" using 3 by metis
moreover have "?d a \<subseteq> N" using assms lll81 by simp
moreover have "?d {(x, Y2)}={x}" by simp
ultimately moreover have "?r (?a2\<inverse>) \<subseteq> N \<union> {x}" using paste_Domain
by (smt Domain_insert Range_converse Un_iff fst_conv set_rev_mp subsetI)
ultimately have 
13: "?a2\<inverse> \<in> injections (?r ?a2) (N \<union> {x})" using 12
 Domain_converse converse_converse injectionsI by (metis (hide_lams, no_types))
have "Y2 \<inter> \<Union> (?r (a -- x)) = {}" using 4 assms by presburger
moreover have "is_partition (?r (a --x ))" using 5 by (metis is_partition_of_def)
ultimately have "is_partition (insert Y2 (?r (a -- x)))" using partition_extension1 assms
by blast
then have "is_partition (?r (a -- x) \<union> {Y2})" by auto
then have "is_partition (?r ?a2)" by (metis "6")
moreover have "\<Union> (?r ?a2) = \<Union> (?r (a -- x)) \<union> Y2"
by (metis "6" Union_Un_distrib cSup_singleton)
moreover have "... = (G - (a,,,x)) \<union> Y2" by (metis "4")
ultimately have "(?r ?a2) partitions ((G - (a,,,x)) \<union> Y2)"
by (metis "6" Un_commute insert_def is_partition_of_def singleton_conv)
then have "?r ?a2 \<in> ?P (G - (a,,,x) \<union> Y2)" using all_partitions_def by (metis mem_Collect_eq)
then have "(?a2\<inverse>) \<in> injections (?r ?a2) (N \<union> {x}) & ?r ?a2 \<in> ?P (G - (a,,,x) \<union> Y2)"
using 13 by fast
then show ?thesis using possible_allocations_rel_def by auto
qed

lemma lll75: assumes "finite a" "(b::altbids) (xx, yy1) \<le> b (xx, yy2)" shows 
"setsum b ((a::allocation) +< (xx,yy1)) \<le> setsum b (a +< (xx,yy2))"
proof -
  let ?z1="(xx, yy1)" let ?z2="(xx, yy2)" let ?a0="a -- xx" let ?a1="a +< ?z1" let ?a2="a +< ?z2"
  have 
  0: "{?z1} || {xx}={?z1} & {?z2}||{xx}={?z2}" using restrict_def by auto

  have "finite {?z1} & finite {?z2}" by simp then have 
  2: "finite ?a1 & finite ?a2" using paste_def assms 
  by (metis finite_Un finite_insert outside_union_restrict)

  have "?a1 = (?a1 -- xx) \<union> (?a1 || {xx}) " 
  using paste_def Outside_def outside_union_restrict by metis
  have "setsum b ?a1 = setsum b (?a1||{xx}) + setsum b (?a1 outside {xx})" using 2
  by (metis finite_Un lll00 lll01 lll06b outside_union_restrict setsum.union_disjoint)
  moreover have 
  1: "?a1 = a +* {?z1} & ?a2 = a +* {?z2}" by (metis fst_conv snd_conv)
  then have "?a1||{xx} = (a || {xx}) +* ({?z1} || {xx})" using lll71 by fastforce

  moreover have "... = {?z1}||{xx}" using ll41 ll56 by (metis "0" Domain_empty Domain_insert Int_lower2)
  ultimately have 
  "setsum b ?a1 = setsum b ({?z1}) + setsum b (?a1 outside {xx})" 
  by (metis "0") then have
  11: "setsum b ?a1 = b ?z1 + setsum b (?a1 outside {xx})"
  by simp

  have "setsum b ?a2 = setsum b (?a2||{xx}) + setsum b (?a2 outside {xx})" using 2
  by (metis finite_Un lll00 lll01 lll06b outside_union_restrict setsum.union_disjoint)
  have "?a2||{xx} = (a || {xx}) +* ({?z2} || {xx})" using lll71 by fastforce
  moreover have "... = {?z2}||{xx}" using ll41 ll56 by (metis "0" Domain_empty Domain_insert Int_lower2)
  ultimately have "setsum b ?a2 = setsum b ({?z2}) + setsum b (?a2 outside {xx})" using 1 0  by (metis 
  `proceeds b (a +< (xx, yy2)) = proceeds b ((a +< (xx, yy2)) || {xx}) + proceeds b ((a +< (xx, yy2)) -- xx)`) 
  then have
  12: "setsum b ?a2 = b ?z2 + setsum b (?a2 outside {xx})" by simp

  have "?a1 outside {xx} = (a outside {xx}) +* ({?z1} outside {xx})" 
  using lll72 by (metis "1")
  moreover have "... = (a outside {xx}) +* {}" using 1
  by (metis "0" Diff_insert_absorb empty_iff lll04 restrict_empty)
  ultimately have "?a1 outside {xx} = a outside {xx}"
  by (metis Un_empty_right outside_union_restrict paste_outside_restrict restrict_empty)
  moreover have "... = ?a2 outside {xx}" using lll72 0 1 lll04 
  Un_empty_right outside_union_restrict paste_outside_restrict restrict_empty 
  by (metis Diff_cancel) (*MC: Diff_insert_absorb AND empty_iff not needed now??! *)
  ultimately show ?thesis using 11 12 assms by smt
qed
BIGSKIP*)
(*BIGSKIP
lemma lll76: assumes "a \<in> possible_allocations_rel G N"
"n \<in> Range a"
"finite (possibleAllocationsRel (N-{n}) G)"
(* "finite (possible_allocations_rel G (N-{n}))" (*MC: qv allocs_finite *) *)
"finite a" (*MC: the two finiteness requirements can be replaced by finiteness of N, G*)
"EX i. i\<in>Domain (a^-1 -- n) & b (i, (a^-1),,,i) \<le> b (i, (a^-1),,,i \<union> (a^-1),,,n)"
(* MC: this is monotonicity assumption *)
shows "Max (proceeds b ` (converse ` (possible_allocations_rel G (N - {n})))) \<ge> 
proceeds b ((a\<inverse>) -- n)"
proof -
  let ?P=possible_allocations_rel let ?aa="a^-1 -- n" let ?d=Domain let ?Yn="a^-1,,,n"
  let ?p=proceeds let ?X="converse ` (?P G (N-{n}))" let ?u=runiq let ?r=Range 

  have "?u a & ?u (a^-1)" using assms(1) lll81 by blast
  then moreover have "?u ?aa" using subrel_runiq Outside_def by blast
  moreover have "?aa \<subseteq> a^-1" using Outside_def by blast
  then moreover have "?aa^-1 \<subseteq> a" using Outside_def converse_def by (metis converse_subset_swap)
  ultimately have 
  2: "?u ?aa & ?u a & ?u (a^-1) & ?u (?aa^-1)" using subrel_runiq by auto obtain i where 
  0: "i \<in> ?d ?aa & b (i, (a^-1),,,i) \<le> b (i, (a^-1),,,i \<union> ?Yn)" using assms(5) by blast
  let ?Y1="?aa,,,i" let ?Y2="?Y1 \<union> ?Yn"
  
  have "{i} \<inter> {n}={}" using 0 by (metis Diff_iff Int_commute Int_empty_right Int_insert_right_if0 outside_reduces_domain)
  then have "?aa``{i} = (a^-1)``{i}" using 0 Outside_def Image_def lll86 by metis then
  have 
  7: "?Y1=(a^-1),,,i" by simp

  have 
  5: "?d ?aa \<subseteq> N - {n}" using assms lll81 by (metis Diff_mono Range_converse converse_converse outside_reduces_domain subset_refl)
  then have 
  6: "N - {n} \<union> {i} = N -{n}" using 0 by blast
  have
  3: "(?d a) partitions G" using assms lll81 by blast then
  have "is_partition (?r (a^-1))" using is_partition_of_def by (metis Range_converse)
  then have 
  4: "is_partition (?r ?aa)" using all_partitions_def is_partition_of_def 
  Outside_def subset_is_partition lll81 assms by (metis Range_outside_sub equalityE)
  moreover have "?Y1 \<in> (?r ?aa)" using 0 lll82 by (metis "2" eval_runiq_in_Range)
  ultimately have "?Y2 \<noteq> {}" using is_partition_def 0 by (metis Un_empty  inf_bot_right)

  have "{i} \<times> ?aa``{i} = {i} \<times> {?Y1}" using 0 Image_runiq_eq_eval 2 by (metis cSup_singleton)
  moreover have "... = {(i, ?Y1)}" by simp
  ultimately have 
  1: "?aa +< (i, ?Y1) = ?aa" using 0 paste_def eval_rel_def ll84 by (metis fst_conv snd_conv)
  
  have "?r (a^-1) = ?r ?aa \<union> ?r ((a^-1)||{n})" by (metis Range_Un_eq outside_union_restrict)
  moreover have "... = ?r ?aa \<union> (a^-1) `` {n}" by (metis lll85)
  ultimately moreover have "?r ?aa = (a^-1)``(?d (a^-1)-{n})" by (metis lll01 lll85)
  ultimately moreover have "?r (a^-1) = ?r ?aa \<union> (a^-1)``{n}" by simp
  ultimately moreover have "?r ?aa \<inter> (a^-1)``{n} = {}" using lll78
  by (metis "2" converse_converse)
  ultimately have "?r ?aa=?r (a^-1) - (a^-1)``{n}" by blast
  moreover have "a^-1``{n} = {?Yn}"
  by (metis "2" Domain_converse Image_runiq_eq_eval assms(2) lll82)
  ultimately have "?r ?aa = ?r (a^-1) - {?Yn}" by force
  moreover have "{?Yn} \<subseteq> ?r (a^-1)" using assms eval_runiq_in_Range by (metis "2" Domain_converse cSup_singleton empty_subsetI insert_subset runiq_wrt_eval_rel')
  moreover have "\<Union> (?r (a^-1))=G" using assms lll81 is_partition_of_def by (metis Range_converse)
  ultimately
  have "is_partition_of (?r ?aa) (G - ?Yn)" using lll80 3 2 4 
  by (metis `is_partition (Range (a\<inverse>))` cSup_singleton)
  moreover have "?u ?aa" by (metis "2")
  moreover have "?u (?aa^-1)" using 2 by fast
  moreover have "?d ?aa \<subseteq> (N -{n})" by (metis Diff_mono Domain_converse assms lll81 outside_reduces_domain subset_refl)

  ultimately have "?aa^-1 \<in> ?P (G-?Yn) (N-{n})" using assms lll81 by (metis Domain_converse converse_converse)

  moreover have "?Y2 \<inter> (G -?Yn - ?Y1)={}" by fast
  ultimately have "(?aa +< (i, ?Y2))\<inverse> \<in> ?P (G - ?Yn - ?Y1 \<union> ?Y2) (N-{n} \<union> {i})" 
  using lll74 by (metis `(a\<inverse> -- n) ,,, i \<union> a\<inverse> ,,, n \<noteq> {}`)
  then have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P (G \<union> ?Y2) (N-{n} \<union> {i})" by (smt Un_Diff_cancel Un_commute Un_left_commute)

  moreover have "?Yn \<subseteq> G"
  by (metis Union_upper `\<Union>Range (a\<inverse>) = G` `{a\<inverse> ,,, n} \<subseteq> Range (a\<inverse>)` insert_subset)
  moreover have "\<Union> (?r ?aa) \<subseteq> G"
  by (metis Diff_subset Sup_subset_mono `Range (a\<inverse> -- n) = Range (a\<inverse>) - {a\<inverse> ,,, n}` `\<Union>Range (a\<inverse>) = G`)
  then moreover have "?Y1 \<subseteq> G" 
  by (metis Sup_le_iff `(a\<inverse> -- n) ,,, i \<in> Range (a\<inverse> -- n)`)
  ultimately moreover have "?Y2 \<subseteq> G" by simp
  ultimately have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P G ((N-{n}) \<union> {i})" by (metis Un_absorb2)
  then have 
  "(?aa +< (i, ?Y2))\<inverse> \<in> ?P G (N-{n})" using 6 by force
  then have "?aa +< (i, ?Y2) \<in> ?X" by (metis converse_converse image_eqI)
  then have "?p b (?aa +< (i, ?Y2)) \<in> (?p b)`?X" by blast
  moreover have "finite (?p b ` ?X)" using assms(3) by (metis finite_imageI)
  ultimately have "?p b (?aa +< (i, ?Y2)) \<le> Max ((?p b) ` ?X)" using Max_ge by blast
  moreover have "b (i, ?Y1) \<le> b (i, ?Y2)" using 7 0 by presburger
  moreover have "finite ?aa" using assms(4) by (metis `a\<inverse> -- n \<subseteq> a\<inverse>` finite_converse finite_subset)
  ultimately moreover have " ?p b (?aa +< (i, ?Y2)) \<ge> ?p b (?aa +< (i, ?Y1))" using lll75
  by blast
  ultimately show ?thesis  using 1 by force
qed


corollary lm01:
assumes "a \<in> possibleAllocationsRel N G"
"n \<in> Domain a"
"finite (possibleAllocationsRel (N-{n}) G)" (*MC: qv allocs_finite *)
"finite a" (*MC: the two finiteness requirements can be replaced by finiteness of N, G*)
"EX i. i\<in>Domain (a -- n) & b (i, a,,,i) \<le> b (i, a,,,i \<union> a,,,n)"
(* MC: this is monotonicity assumption *)
shows "alpha N G b n \<ge> 
proceeds b (a -- n)" using lll76 assms converse_def 
proof -
  let ?p="possible_allocations_rel" let ?a="a^-1" let ?f=finite
  have "?a \<in> ?p G N" using assms by fastforce
  moreover have "n \<in> Range ?a" using assms
by fast
  moreover have "?f ?a" using assms by fast
  moreover have 
"EX i. i\<in>Domain (?a^-1 -- n) & b (i, (?a^-1),,,i) \<le> b (i, (?a^-1),,,i \<union> (?a^-1),,,n)"
using assms 
by simp
ultimately have 
"Max (proceeds b ` (converse ` (?p G (N - {n})))) \<ge> 
proceeds b ((?a\<inverse>) -- n)" using lll76 assms by blast
thus ?thesis by simp
qed

corollary lm08: assumes 
"a \<in> winningAllocationsRel N G b"
"n \<in> Domain a"
"finite (possibleAllocationsRel (N-{n}) G)"
"finite a"
"EX i. i\<in>Domain (a -- n) & b (i, a,,,i) \<le> b (i, a,,,i \<union> a,,,n)"
(* MC: this is monotonicity assumption *)
shows "alpha N G b n \<ge> 
proceeds b (a -- n)" using assms lm01 lm03 by simp

corollary assumes 
"isChoice (graph {winningAllocationsRel N G b} (t::tieBreaker))"
"n \<in> Domain (winningAllocationRel N G t b)" 
"finite (possibleAllocationsRel (N-{n}) G)"
"finite (winningAllocationRel N G t b)"
"EX i. i\<in>Domain ((winningAllocationRel N G t b) -- n) & 
b (i, (winningAllocationRel N G t b),,,i) \<le> 
b (i, (winningAllocationRel N G t b),,,i \<union> (winningAllocationRel N G t b),,,n)"
shows "alpha N G b n \<ge> remainingValueRel N G t b n"
using lm08 assms lm07 by blast
BIGSKIP *)

(* abbreviation "vcga N G b == map (toPartialAllo) (winningAllocationsAlg (N \<union> {auctioneer}) G (toFullBid (set G) b))" *)
(* abbreviation "addedBidder (N::participant set) == Min (-N)" *)
(*abbreviation "addedBidder (N::participant set) == 1 + Max N"*)

(* abbreviation "allAllocations' N \<Omega> == 
allInjections \<inter> {a. Domain a \<subseteq> (N \<union> {addedBidder'}) & Range a \<in> all_partitions \<Omega>}" *)

(* abbreviation "extendedBid N \<Omega> b == (({addedBidder'} \<times> (Pow \<Omega>)) :== (%x. (0))) b"
abbreviation "maximalAllocations' N \<Omega> b == arg_max' (setsum (extendedBid N \<Omega> b)) (allAllocations' N \<Omega>)" *)
(* MC: extendedBid superfluous here? *)
(*abbreviation "maximalAllocations''' G b == arg_max' (setsum' b) (allAllocations' (Participants b) G)"*)

(* abbreviation "alpha' N G b == (alpha N G) \<circ> (toFullBid G)" 
abbreviation "Vcga N G b t == toPartialAllo (t (Vcgas N G b))"
abbreviation "alpha' N G b == alpha (N\<union>{auctioneer}) G (toFullBid G b)"
abbreviation "alphaAlg' N G b == alphaAlg (N\<union>{auctioneer}) G (toFullBid (set G) b)"
abbreviation "vcgp N G b t n == alpha' N G b n - 
(setsum (toFullBid G b) ((winningAllocationRel (N \<union> {auctioneer}) G t (toFullBid G b)) -- n))"
abbreviation "Vcgp N G b t n == alphaAlg' N G b n - 
(setsum (toFullBid (set G) b) ((winningAllocationAlg (N \<union> {auctioneer}) G t (toFullBid (set G) b)) -- n))"
(*MC: t must come first of toPartialAllo due to how we implemented tie breaking (homogeneously)*)
*)
(*abbreviation "argmax' f A == { x \<in> A . f x = Max (f ` A) }"
abbreviation "Vcga' N G R b == arg_max' (setsum (resolvingBid N G b R)) (set (Vcgas N G b))"
abbreviation "vcgp'' N G b r n == alpha' N (set G) b n - 
(setsum (toFullBid (set G) b) (vcga' N G b r -- n))" *)

(* abbreviation "randomBids N \<Omega> b random==resolvingBid (N\<union>{addedBidder'}) \<Omega> (extendedBid N (set \<Omega>) b) random" *)

(*
abbreviation "vcga'' N \<Omega> b random == (\<Union>((arg_max' (setsum (randomBids N \<Omega> b random)) (maximalAllocations' N (set \<Omega>) b))))--(addedBidder')"
*)
(* abbreviation "vcgp' N \<Omega> b random n ==
(Max (setsum b ` (allAllocations' (N-{n}) (set \<Omega>)))) - (setsum b (vcga'' N \<Omega> b random -- n))"
*)
(*abbreviation "vcga''' G b r == \<Union>
(arg_max' (setsum (randomBids (Participants b) G (toFunction b) r )) (maximalAllocations''' (set G) b)) 
-- (addedBidder (Participants b))"*)

(*lemma nn21: "maximalAllocations''' \<Omega> b' \<subseteq> allAllocations' (Participants b') \<Omega>" by auto*)
(* abbreviation "chosenAllocation' N G bids random == 
hd(perm2 (takeAll (%x. x\<in>(maximalStrictAllocations' N (set G) bids)) (possibleAllocationsAlg3 
({addedBidder'}\<union>N) G)) random)"
abbreviation "randomBids' N b G r == tiebids' (chosenAllocation' N G b r)
({addedBidder'}\<union>N) (set G)"
*)


(*
abbreviation "toStrict G allo == allo \<union> {(addedBidder (Domain allo),
(G-\<Union>Range allo) \<union> allo,,,(addedBidder (Domain allo)))}"

lemma nn54a: assumes "a1 \<noteq> a2" "addedBidder (Domain a1) \<notin> (Domain a1) \<union> Domain a2" shows "toStrict G a1 \<noteq> toStrict G a2" 
using assms by blast

lemma nn54b: assumes "toStrict G a1 \<noteq> toStrict G a2" "addedBidder (Domain a1) \<notin> (Domain a1) \<union> Domain a2" 
shows "a1 \<noteq> a2" using assms by fast

corollary nn54: assumes "addedBidder (Domain a1) \<notin> (Domain a1) \<union> Domain a2" shows
"a1 \<noteq> a2 = (toStrict G a1 \<noteq> toStrict G a2)" using assms nn54a nn54b by auto 
*)


(*
lemma 
assumes "finite (Participants b)" "distinct G" "set G \<noteq> {}" shows
"chosenAllocation' G b r \<in> maximalStrictAllocations' (set G) b" using mm82 sorry

corollary
assumes "finite G" "(a::('a::linorder\<times>_)set) \<in> allStrictAllocations' N G" 
"aa \<in> allStrictAllocations' N G" "aa \<noteq> a" shows 
"setsum' (tiebids' a N G) aa < setsum' (tiebids' a N G) a"

corollary mm70e: 
assumes "finite G" 
"addedBidder' \<notin> N"
"a \<in> allAllocations' N G" "aa \<in> allAllocations' N G" "aa \<noteq> a" shows
"setsum' (tiebids' (toStrict G a) (N \<union> {addedBidder'}) G) (toStrict G aa) <
setsum' (tiebids' (toStrict G a) (N \<union> {addedBidder'}) G) (toStrict G a)"
proof -
let ?s=toStrict let ?a="?s G a" let ?aa="?s G aa" let ?S="possibleAllocationsRel (N\<union>{addedBidder'}) G"
have "finite G" using assms(1) 
by simp
moreover have "?a \<in> ?S" using assms sorry
moreover have "?aa \<in> ?S" using assms sorry
moreover have "?aa \<noteq> ?a" using assms nn54 sorry ultimately moreover have 
5: "setsum (tiebids ?a (N\<union>{addedBidder'}) G) ?aa < setsum (tiebids ?a (N\<union>{addedBidder'}) G) ?a" 
by (rule mm70d)
moreover have 
7: "Domain (tiebids' ?a (N\<union>{addedBidder'}) G)=(N\<union>{addedBidder'}) \<times> (Pow G - {{}})"
using mm64 by blast
ultimately moreover have 
6: "?a \<subseteq> (N\<union>{addedBidder'}) \<times> (Pow G - {{}})
& ?aa \<subseteq> (N\<union>{addedBidder'}) \<times> (Pow G - {{}})
" using mm63c 
by (metis (mono_tags))
let ?f="tiebids' ?a (N\<union>{addedBidder'}) G"
let ?ff="tiebids ?a (N\<union>{addedBidder'}) G"
have 
0: "finite ?a" sorry
have 
1: "runiq ?f" sorry
have 
3: "setsum (toFunction ?f) (?a \<inter> Domain ?f) =
setsum' ?f ?a" using 0 1 by (rule nn48d)
have 
2: "finite ?aa" sorry
have 
4: "setsum (toFunction ?f) (?aa \<inter> Domain ?f) =
setsum' ?f ?aa" using 2 1 by (rule nn48d)
have "?a \<subseteq> Domain ?f & ?aa \<subseteq> Domain ?f" using 6 7 by presburger
then have "?a \<inter> Domain ?f = ?a & ?aa \<inter> Domain ?f = ?aa" by blast
then have "setsum ?ff (?aa\<inter>Domain ?f) < setsum ?ff (?a\<inter>Domain ?f)" using 5 
by presburger
then show ?thesis using 3 4 5 6 nn55 by simp
qed


lemma nn07: "\<forall>x \<in> ({auctioneer} \<times> t). (toFullBid G b) x = (%x. 0) x" sorry 

lemma nn08: assumes "finite ({auctioneer} \<times> t)" 
"\<forall>x \<in> ({auctioneer} \<times> t). (toFullBid G b) x = ((%x. 0) x)" 
shows
"setsum (toFullBid G b) ({auctioneer} \<times> t) = setsum (%x. 0) ({auctioneer} \<times> t)" 
using assms by (smt setsum.neutral)

corollary nn09: assumes "trivial t" shows "setsum (toFullBid G b) ({auctioneer} \<times> t) = 0"
using assms nn07 nn08 lm54 sorry

corollary nn09b: "condition1 (toFullBid G b) auctioneer" using assms nn09 by auto

corollary nn10: assumes
"condition1 (toFullBid G b) auctioneer" 
"n \<noteq> auctioneer"
"finite (N \<union> {auctioneer})"
"finite G"
"isChoice (graph {winningAllocationsRel (N\<union>{auctioneer}) G (toFullBid G b)} (t::tieBreaker))"
shows "alpha (N\<union>{auctioneer}) G (toFullBid G b) n \<ge> remainingValueRel (N\<union>{auctioneer}) G t (toFullBid G b) n" 
using assms lm61c by auto

corollary nn10b: assumes "n \<noteq> auctioneer" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel (N\<union>{auctioneer}) G (toFullBid G b)} (t::tieBreaker))"
shows 
"alpha' N G b n \<ge> ((remainingValueRel (N\<union>{auctioneer}) G t (toFullBid G b) n)::price)"
using assms nn10 nn09b by force

lemma nn10c: "x - y >=0 = ((x::price) >= y)" by fastforce

corollary nn10d: assumes "n \<noteq> auctioneer" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel (N\<union>{auctioneer}) G (toFullBid G b)} (t::tieBreaker))"
shows "alpha' N G b n - remainingValueRel (N\<union>{auctioneer}) G t (toFullBid G b) n >=0" 
using assms nn10b nn10c by presburger

lemma nn10e: assumes "f x \<in> x" shows "isChoice (graph {x} f)" by (metis (full_types) Collect_mem_eq assms empty_iff insert_iff lm72)

corollary nn10f: assumes "n \<noteq> auctioneer" "finite N" "finite G"
"isChoice (graph {winningAllocationsRel (N\<union>{auctioneer}) G (toFullBid G b)} (t::tieBreaker))"
shows "vcgp N G b t n >= 0" using assms nn10d by blast

corollary assumes "n \<noteq> auctioneer" "finite N" "finite G" "t (vcgas' N G b) \<in> vcgas' N G b"
shows "vcgp N G b t n >= 0" using assms nn10e nn10f by (metis (lifting)) 

corollary assumes "a \<in> vcgas' N G b" 
shows "(Range a) partitions G" using assms lm47 is_partition_of_def 
by (metis (lifting, no_types) lm03 subsetD)
*)


lemma assumes "finite G" "a \<in> allStrictAllocations' (Participants b) G" shows 
"setsum' b a = setsum (toFunction b) a" using assms nn48d sorry


lemma assumes "addedBidder' \<notin> N" shows "arg_max' (setsum (resolvingBid N G bids (nat random))) (arg_max' (setsum bids) (possibleAllocationsRel N (set G))) = 
arg_max' (setsum (resolvingBid N G bids (nat random))) (arg_max' (setsum bids) (allAllocations'''' N (set G)))"
using assms sorry


corollary nn45b: assumes "a \<in> allAllocations' N G" shows "is_partition (Range a)"
using assms nn45a sorry


lemma nn46: assumes "a \<in> allAllocations'''' N G" shows "runiq a & runiq (a^-1)" using assms nn28e
Int_iff mem_Collect_eq sorry

corollary assumes "a \<in> allAllocations' N (G::good set)" "(n1::participant) \<in> Domain a" "n2 \<in> Domain a"  shows
"(a,,n1) \<inter> (a,,n2) = {}" sorry

corollary assumes "a \<in> allAllocations' N G" "n1 \<in> Domain a" "n2 \<in> Domain a" "n1 \<noteq> n2" shows
"(a,,n1) \<inter> (a,,n2) = {}" using assms nn45a eval_runiq_in_Range nn46 is_partition_def 
is_partition_of_def nn45b
proof - have "runiq a & runiq (a^-1)" using assms nn28e sorry
then have "a,,n1 \<noteq> a,,n2" using assms 
by (metis converse_iff eval_runiq_rel runiq_imp_uniq_right_comp)
moreover have "a,,n1 \<in> Range a & a,,n2 \<in> Range a" using assms 
by (metis `runiq a \<and> runiq (a\<inverse>)` eval_runiq_in_Range)
moreover have "is_partition (Range a)" sorry
ultimately show ?thesis using assms is_partition_def by metis
qed


(*
text {* The image of the domain of a right-unique relation @{term R} under @{term R}
  is the image of the domain under the function that corresponds to the relation. *}
corollary runiq_imp_eval_eq_Im:
  assumes "runiq R"
  shows "R `` Domain R = (eval_rel R) ` Domain R" using assms lm025 by fast

text {* The cardinality of the range of a finite, right-unique relation is less or equal the 
  cardinality of its domain. *}
lemma card_Range_le_Domain:
  assumes finite_Domain: "finite (Domain R)"
      and runiq: "runiq R"
  shows "card (Range R) \<le> card (Domain R)"
proof -
  have "Range R = R `` Domain R" by blast
  also have "\<dots> = (eval_rel R) ` Domain R" using runiq by (rule runiq_imp_eval_eq_Im)
  finally have "Range R = (eval_rel R) ` Domain R" .
  then show ?thesis using finite_Domain by (metis card_image_le)
qed
*)

(*
proof -
  have "Collect (op < (f x)) \<inter> f ` X \<noteq> {}" using assms(2) assms(3) by blast
  thus "x \<notin> argmax f X" using assms(1) not_less by fastforce
qed
 argmax.simps mem_Collect_eq
Max_eqI finite_imageI image_iff
Diff_iff empty_iff insert_iff less_imp_le not_less*)
(*
lemma mm80b: assumes "finite X" "mx \<in> X" "\<forall>x \<in> X. f x <= f mx" shows "f mx = Max (f ` X)"
proof -
  have "X \<noteq> {}" using assms(2) by blast
  hence "Max (f ` X) \<le> max (f mx) (f mx)" using assms(1) assms(3) by auto
  thus "f mx = Max (f ` X)" using antisym assms(1) assms(2) by fastforce
qed

lemma mm80bb: assumes "finite X" "mx \<in> X" "\<forall>x \<in> X. f x <= f mx" shows "mx \<in> argmax f X"
using assms mm79 mm80b IntI by (metis (erased, hide_lams) vimage_singleton_eq)

lemma mm80bbb: assumes "finite X" "mx \<in> X" "\<forall>x \<in> X-{mx}. f x < f mx" shows "mx \<in> argmax f X"
using assms mm80bb 
by (metis (mono_tags, hide_lams) Diff_iff eq_iff less_imp_le singleton_iff)
*)


(*
lemma assumes "\<forall>x. trivial ({x}\<times>(P``{x}))"
shows "runiq P" unfolding runiq_def finestpart_def
using ll40 lm006 finestpart_def runiq_def lm007
sorry

lemma assumes "runiq P" shows "trivial (({x}\<times>UNIV)\<inter>P)" 
unfolding runiq_def 
using assms trivial_def runiq_def ll40 sorry

lemma (* lm012: *) "(runiq P) = (\<forall>x. trivial ({x}\<times>(P``{x})))" unfolding runiq_def finestpart_def
using ll40 lm006 finestpart_def sorry

lemma (* lm005: *) "runiq P = (\<forall>x. trivial (({x}\<times>UNIV)\<inter>P))" 
(* unfolding trivial_def runiq_def *) using (* lm012 *) lm002 sorry

lemma "runiq R \<longleftrightarrow> (\<forall> x y y' . (x, y) \<in> R \<and> (x, y') \<in> R \<longrightarrow> y = y')" unfolding runiq_def 
lm01 lm00 using runiq_def lm00 lm01 sorry
(*by (metis ImageI Image_def Image_iff all_not_in_conv empty_iff insert_iff mem_Collect_eq singletonI subsetCE subsetI)*)

lemma assumes "runiq P" "runiq Q" "\<forall>x\<in>Domain P \<inter> (Domain Q). P``{x} \<subseteq> Q``{x}" shows 
"runiq (P \<union> Q)" unfolding lll33 fst_eq_Domain using assms lll33 fst_eq_Domain disj_Un_runiq lm010 sorry
(* lll33 runiq_alt runiq_basic fst_eq_Domain lm011 lm010 inj_on_def
IntI Un_iff empty_iff image_eqI lm010c *)

lemma assumes "runiq P" "runiq Q" "Domain P \<inter> (Domain Q) \<subseteq> Domain (P \<inter> Q)" shows 
"runiq (P \<union> Q)" unfolding lll33 using assms lll33 runiq_alt runiq_basic fst_eq_Domain 
disj_Un_runiq lm010 inj_on_def IntI Un_iff empty_iff image_eqI sorry
*)

(*
lemma runiq_imp_triv_singleton_Im:
  fixes x
  assumes runiq: "runiq R"
  shows "trivial (R `` {x})"
proof -
  fix x::'a
  have "trivial {x}" unfolding trivial_def by simp
  with runiq show "trivial (R `` {x})" unfolding runiq_def by fast
qed
*)
(*
lemma triv_singleton_Im_imp_runiq:
  assumes triv: "\<forall> x . trivial (R `` {x})"
  shows "runiq R" using assms by (metis runiq_alt)
*)


(*
lemma runiq_alt: "runiq R \<longleftrightarrow> (\<forall> x . trivial (R `` {x}))"
(* CL: The following proof, found by Sledgehammer without taking into account the two lemmas above,
   takes 26 ms on my machine. *)
(* unfolding runiq_def by (metis Image_empty trivial_cases trivial_empty trivial_singleton) *)
proof
  assume "runiq R"
  then show "\<forall> x . trivial (R `` {x})" by (metis runiq_imp_triv_singleton_Im)
next
  assume triv: "\<forall> x . trivial (R `` {x})"
  then show "runiq R" by (rule triv_singleton_Im_imp_runiq)
qed
*)


(*
lemma runiq_wrt_eval_rel:
  fixes R :: "('a \<times> 'b) set"
  shows "runiq R \<longleftrightarrow> (\<forall>x . R `` {x} \<subseteq> {R ,, x})"
unfolding runiq_alt trivial_def by simp
*)

(* Image_within_domain' *)

(*
(* TODO CL: document *)
lemma runiq_imp_ex1_right_comp:
  fixes a
  assumes "runiq R"
      and "a \<in> Domain R"
  shows "\<exists>! b . (a, b) \<in> R"
using assms by (metis Domain.cases l31)

(* TODO CL: document *)
lemma ex1_right_comp_imp_runiq:
  assumes "\<forall> a \<in> Domain R . \<exists>! b . (a, b) \<in> R"
  shows "runiq R"
using assms
  (* TODO CL: This step takes 136 ms in Isabelle2013-1-RC3; optimise manually. *)
by (metis Domain.simps runiq_basic)
*)

(* TODO CL: document *)


lemma runiq_relation_except_singleton:
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R\<inverse>)"
      and Range: "z \<in> Range R"
  shows "{ (x, y) . (x, y) \<in> R \<and> x \<noteq> (THE x . (x, z) \<in> R) }
    = { (x, y) . (x, y) \<in> R \<and> y \<noteq> z }"
proof (rule equalitySubsetI)
  fix tup
  assume "tup \<in> { (x, y) . (x, y) \<in> R \<and> x \<noteq> (THE x . (x, z) \<in> R) }"
  then obtain x y where tup_def: "tup = (x, y)" and tup_R: "(x, y) \<in> R" and x_not_R_z: "x \<noteq> (THE x . (x, z) \<in> R)" by blast
  from runiq_conv x_not_R_z have "y \<noteq> z"
    (* TODO CL: optimise: takes 612 ms in Isabelle2013-1-RC3 *)
    by (metis (lifting) converse_iff runiq_basic the_equality tup_R)
  with tup_def tup_R show "tup \<in> { (x, y) . (x, y) \<in> R \<and> y \<noteq> z }" by fastforce
next
  fix tup
  assume "tup \<in> { (x, y) . (x, y) \<in> R \<and> y \<noteq> z }"
  then obtain x y where tup_def: "tup = (x, y)" and tup_R: "(x, y) \<in> R" and y_ne_z: "y \<noteq> z" by blast
  from tup_R y_ne_z have "x \<noteq> (THE x . (x, z) \<in> R)" 
    (* TODO CL: optimise: takes 111 ms in Isabelle2013-1-RC3 *)
    by (metis (lifting, no_types) Range RangeE runiq runiq_basic runiq_conv runiq_conv_wrt_THE the_equality)
  with tup_def tup_R show "tup \<in> { (x, y) . (x, y) \<in> R \<and> x \<noteq> (THE x . (x, z) \<in> R) }" by fastforce
qed


lemma Domain_runiq_Diff_singleton:
  assumes runiq: "runiq R"
      and in_rel: "(x, y) \<in> R"
  shows "Domain (R - {(x, y)}) = Domain R - {x}"
(* TODO CL: One should think this is easy, but Sledgehammer in Isabelle2013-1-RC3 can't prove it at all. *)
proof
  show "Domain (R - {(x, y)}) \<subseteq> Domain R - {x}"
  proof
    fix z
    assume assm: "z \<in> Domain (R - {(x, y)})"
    show "z \<in> Domain R - {x}"
    proof
      show "z \<in> Domain R" using assm by blast
      show "z \<notin> {x}"
      proof
        assume "z \<in> {x}"
        with assm obtain y' where "(x, y') \<in> R - {(x, y)}" by blast
        then have "(x, y') \<in> R" and "y' \<noteq> y" by simp_all
        from runiq in_rel `(x, y') \<in> R` have "y = y'" by (metis l31)
        with `y' \<noteq> y` show False by simp
      qed
    qed
  qed
next
  have "Domain R - {x} = Domain R - Domain {(x, y)}" by blast
  also have "\<dots> \<subseteq> Domain (R - {(x, y)})" by (rule Domain_Diff_subset)
  finally show "Domain R - {x} \<subseteq> Domain (R - {(x, y)})" .
qed


(*
text {* Any non-empty set has at least one partition. *}
lemma non_empty_set_has_partitions:
  assumes "A \<noteq> {}"
  shows "all_partitions A \<noteq> {}"
(* CL: the following takes 1.32 s on my machine with Isabelle2013, and it does already use my lemma set_partitions_itself:
unfolding all_partitions_def is_partition_of_def is_partition_def 
by (smt Int_absorb Int_commute assms empty_def is_partition_of_def mem_Collect_eq set_partitions_itself singleton_conv2) *)
(* CL: Isabelle2013-1-RC1 finds the following, which takes 16 ms:
by (metis all_partitions_def assms equals0D mem_Collect_eq set_partitions_itself) *)
(* CL: Without set_partitions_itself, it doesn't work within reasonable time
   (tested with Isabelle2013 with unfolding; tested with Isabelle2013-1-RC1 without unfolding)
   unfolding all_partitions_def is_partition_of_def is_partition_def sledgehammer (del: set_partitions_itself) *)
proof
  assume "all_partitions A = {}"
  then have "\<forall> P . \<not>is_partition_of P A" using all_partitions_def by blast
  moreover have "is_partition_of {A} A" using assms by (rule set_partitions_itself)
  ultimately show False by simp
qed
*)


(*
text {* The image of the domain of a right-unique relation @{term R} under @{term R}
  is the image of the domain under the function that corresponds to the relation. *}
corollary runiq_imp_eval_eq_Im:
  assumes "runiq R"
  shows "R `` Domain R = (eval_rel R) ` Domain R" using assms lm025 by fast

text {* The cardinality of the range of a finite, right-unique relation is less or equal the 
  cardinality of its domain. *}
lemma card_Range_le_Domain:
  assumes finite_Domain: "finite (Domain R)"
      and runiq: "runiq R"
  shows "card (Range R) \<le> card (Domain R)"
proof -
  have "Range R = R `` Domain R" by blast
  also have "\<dots> = (eval_rel R) ` Domain R" using runiq by (rule runiq_imp_eval_eq_Im)
  finally have "Range R = (eval_rel R) ` Domain R" .
  then show ?thesis using finite_Domain by (metis card_image_le)
qed

text {* There is an injective function from a finite set to any set of a greater cardinality. *}
lemma injections_exist:
  fixes X::"'a set"
    and Y::"'b set"
  assumes finiteX: "finite X"
      and finiteY: "finite Y"
  shows "card X \<le> card Y \<Longrightarrow> injections X Y \<noteq> {}"
using finiteX
proof induct
  case empty
  have "{} \<in> injections {} Y"
  proof (rule injectionsI)
    show "Domain {} = {}" by simp
    show "Range {} \<subseteq> Y" by simp
    show "runiq {}" by (rule runiq_emptyrel)
    show "runiq ({}\<inverse>)" by (simp add: runiq_emptyrel)
  qed
  then show ?case using assms by fast
next
  case (insert a X)
  then obtain R where R: "R \<in> injections X Y" by auto
  from R have "runiq R" unfolding injections_def by fast
  from R have Domain: "Domain R = X" unfolding injections_def by fast
  from R have Range: "Range R \<subseteq> Y" unfolding injections_def by fast

  from Domain have "card X = card (Domain R)" by fast
  also have "\<dots> \<ge> card (Range R)"
    using insert.hyps(1) Domain `runiq R` card_Range_le_Domain by blast
  finally have "card X \<ge> card (Range R)" .
  moreover have "card Y > card X" using insert.hyps insert.prems by force
  ultimately have *: "card Y > card (Range R)" by (rule order_le_less_trans)

  from finiteY Range have "finite (Range R)" by (rule rev_finite_subset)
  then have "card (Y - Range R) > 0" using * by (rule card_diff_gt_0)
  then have "Y - Range R \<noteq> {}" by force
  then have sup_rels_non_empty: "sup_rels_from R a Y \<noteq> {}"
    unfolding sup_rels_from_def by (auto simp: image_Collect_mem)
  then have **: "\<Union> { sup_rels_from P a Y | P . P \<in> injections X Y } \<noteq> {}"
    using R by (auto simp: Union_map_non_empty)

  from insert have "a \<notin> X" by simp
  then have "injections (insert a X) Y = \<Union> { sup_rels_from P a Y | P . P \<in> injections X Y }"
    by (rule injections_paste)
  with ** show "injections (insert a X) Y \<noteq> {}" by presburger
qed
*)


(*
text {* Extending a right-unique relation by one pair leaves it right-unique
  if the first component of the pair has not been in the domain of the relation already. *}
lemma runiq_extend_singleton:
  assumes runiq: "runiq R"
      and not_in_Domain: "x \<notin> Domain R"
  shows "runiq (R \<union> {(x, y)})"
(* Sledgehammer in Isabelle2013-1-RC3 finds a proof that takes 112 ms. *)
using runiq
proof (rule disj_Un_runiq)
  show "runiq {(x, y)}" by (rule runiq_singleton_rel)
  have "Domain {(x, y)} = {x}" by simp
  with not_in_Domain show "Domain R \<inter> Domain {(x, y)} = {}" by simp
qed

text {* Replacing the second component of one pair in a right-unique relation
  leaves it right-unique. *}
lemma runiq_replace_snd:
  assumes runiq: "runiq R"
      and not_in_Domain: "x \<notin> Domain (R - {(x, y)})"
  shows "runiq (R - {(x, y)} \<union> {(x, z)})"
proof -
  from runiq have "runiq (R - {(x, y)})" by (rule runiq_except)
  then show ?thesis using not_in_Domain by (rule runiq_extend_singleton)
qed

text {* Replacing the first component of a pair in a right-unique relation leaves the relation
  right-unique if the replacement has not been in the domain of the relation before. *}
lemma runiq_replace_fst:
  assumes runiq: "runiq R"
      and not_in_Domain: "z \<notin> Domain R"
  shows "runiq (R - {(x, y)} \<union> {(z, y)})"
proof (rule runiq_extend_singleton)
  from runiq show "runiq (R - {(x, y)})" by (rule runiq_except)
  from not_in_Domain show "z \<notin> Domain (R - {(x, y)})" by blast
qed
*)

(*
text {* Replacing the second component of one pair in a right-unique relation
  leaves it right-unique. *}
lemma runiq_replace_snd':
  assumes runiq: "runiq R"
      and in_rel: "(x, y) \<in> R"
  shows "runiq (R - {(x, y)} \<union> {(x, z)})"
using runiq
proof (rule runiq_replace_snd)
  from runiq in_rel show "x \<notin> Domain (R - {(x, y)})" by (rule runiq_Diff_singleton_Domain)
qed
*)

(*
text {* Extending a relation, whose converse is right-unique, by one pair leaves its converse
  right-unique if the second component of the pair has not been in the range of the relation already. *}
lemma runiq_conv_extend_singleton:
  assumes runiq_conv: "runiq (R\<inverse>)"
      and not_in_Domain: "y \<notin> Range R"
  shows "runiq ((R \<union> {(x, y)})\<inverse>)"
proof -
  from not_in_Domain have "y \<notin> Domain (R\<inverse>)" by simp
  with runiq_conv have "runiq (R\<inverse> \<union> {(y, x)})" by (rule runiq_extend_singleton)
  moreover have "R\<inverse> \<union> {(y, x)} = (R \<union> {(x, y)})\<inverse>" by fast
  ultimately show ?thesis by simp
qed


text {* Replacing the first component of one pair in a relation, whose converse is right-unique,
  leaves its converse right-unique. *}
lemma runiq_conv_replace_fst:
  assumes runiq_conv: "runiq (R\<inverse>)"
      and not_in_Range: "y \<notin> Range (R - {(x, y)})"
  shows "runiq ((R - {(x, y)} \<union> {(z, y)})\<inverse>)"
proof -
  from not_in_Range have "y \<notin> Domain (R\<inverse> - {(y, x)})" by blast
  with runiq_conv have "runiq (R\<inverse> - {(y, x)} \<union> {(y, z)})" by (rule runiq_replace_snd)
  moreover have "R\<inverse> - {(y, x)} \<union> {(y, z)} = (R - {(x, y)} \<union> {(z, y)})\<inverse>" by fast
  ultimately show ?thesis by simp
qed

(* TODO CL: document, and choose better name *)
lemma runiq_conv_Diff_singleton_Range:
  assumes runiq_conv: "runiq (R\<inverse>)"
      and in_rel: "(x, y) \<in> R"
  shows "y \<notin> Range (R - {(x, y)})"
proof -
  from in_rel have "(y, x) \<in> R\<inverse>" by simp
  with runiq_conv have "y \<notin> Domain (R\<inverse> - {(y, x)})" by (rule runiq_Diff_singleton_Domain)
  then show ?thesis by fast
qed

text {* Replacing the first component of one pair in a relation, whose converse is right-unique,
  leaves its converse right-unique. *}
lemma runiq_conv_replace_fst':
  assumes runiq_conv: "runiq (R\<inverse>)"
      and in_rel: "(x, y) \<in> R"
  shows "runiq ((R - {(x, y)} \<union> {(z, y)})\<inverse>)"
using runiq_conv                    
proof (rule runiq_conv_replace_fst)
  from runiq_conv in_rel show "y \<notin> Range (R - {(x, y)})" by (rule runiq_conv_Diff_singleton_Range)
qed
*)
(*
lemma converse_Image: 
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R\<inverse>)"
shows "R\<inverse> `` R `` X \<subseteq> X"
proof -
  have "(R O R\<inverse>) `` X = (\<Union>x \<in> X . (R O R\<inverse>) `` {x})" by (rule Image_eq_UN)
  also have "\<dots> = (\<Union>x\<in>X. R\<inverse> `` R `` {x})" by blast
  also have "\<dots> \<subseteq> (\<Union>x \<in> X. {x})" using converse_Image_singleton assms by fast
  also have "\<dots> = X" by simp
  finally show ?thesis by fast
qed
*)


(* TODO CL: check how much of the following we still need 
section {* Christoph's old stuff *}

text {* A relation is a function on a set @{term A}, if it is left-total on @{term A} and right-unique. *}
definition function_on :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool"
where "function_on R A \<longleftrightarrow> (A \<subseteq> Domain R) \<and> runiq R"

fun as_part_fun :: "('a \<times> 'b) set \<Rightarrow> 'a \<rightharpoonup> 'b"
where "as_part_fun R a = (let im = R `` {a} in 
        if card im = 1 then Some (the_elem im)
        else None)"
*)


(* TODO CL: document if we need this 
lemma
  assumes part: "P partitions A"
      and eq_class_old: "Xold \<in> P" (* Xold is an equivalence class of the old partition *)
      and eq_class_sub: "Xold \<subseteq> Xnew" (* The new equivalence class contains more elements. *)
      and eq_class_ext_new: "(Xnew - Xold) \<inter> A = {}" (* The additional elements are not in the original set. *)
  shows "is_partition (P - {Xold} \<union> {Xnew})"
proof -
  {
    fix X' P' Y' Xold' Xnew' A'
    assume 
        X': "X' \<in> P' - {Xold'} \<union> {Xnew'}"
       and Y': "Y' \<in> P' - {Xold'} \<union> {Xnew'}"
       and eq_class_old': "Xold' \<in> P'"
       and "\<Union> P' = A'"
       and part': "is_partition_of P' A'"
       and eq_class_old': "Xold' \<in> P'"
       and eq_class_ext_new': "(Xnew' - Xold') \<inter> A' = {}"
       and FalseTrue': "X' \<notin> P' \<and> Y' \<in> P'"
    then have "X' \<notin> P'" and "Y' \<in> P'" by simp_all
    from `X' \<notin> P'` have "X' = Xnew'" using X' eq_class_old' by fast
    then have "Y' \<in> P' - {Xold'}" using Y' by (metis FalseTrue' Un_commute Un_empty_left Un_insert_left insert_iff)
    {
      fix x assume "x \<in> Xnew'"
      then have "\<not>(\<exists> Z . Z \<in> P' - {Xold'} \<and> x \<in> Z)"
      proof (cases "x \<in> Xold'")
        case True
        with eq_class_old' part' show ?thesis using is_partition_of_def is_partition_def 
        Diff_iff IntI Int_absorb all_not_in_conv insert_iff by (metis(no_types))
      next
        case False
        then have "x \<in> Xnew' - Xold'" using `x \<in> Xnew'` by simp
        then have "x \<notin> A'" using eq_class_ext_new' by blast
        with `\<Union> P' = A'` show ?thesis by blast
      qed
    }
    then have "X' \<inter> Y' = {}" using `X' = Xnew'` `Y' \<in> P' - {Xold'}` by blast
    then have "X' \<inter> Y' \<noteq> {} \<longleftrightarrow> X' = Y'" using FalseTrue' by blast
  }
  note foo = this
  have "\<Union> P = A" using part unfolding is_partition_of_def ..
  {
    fix X Y
    assume X: "X \<in> P - {Xold} \<union> {Xnew}"
       and Y: "Y \<in> P - {Xold} \<union> {Xnew}"
    have "X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y"
    proof (cases rule: case_split_2_times_2)
      assume "X \<in> P \<and> Y \<in> P"
      with part show ?thesis unfolding is_partition_of_def is_partition_def by force
    next
      assume FalseTrue: "X \<notin> P \<and> Y \<in> P"
      with X Y eq_class_old `\<Union> P = A` part eq_class_old eq_class_ext_new show ?thesis by (rule foo)
    next
      assume TrueFalse: "X \<in> P \<and> Y \<notin> P"
      then have "Y \<notin> P \<and> X \<in> P" by blast
      with Y X eq_class_old `\<Union> P = A` part eq_class_old eq_class_ext_new have "Y \<inter> X \<noteq> {} \<longleftrightarrow> Y = X" by (rule foo)
      then show ?thesis by blast
    next
      assume FalseFalse: "X \<notin> P \<and> Y \<notin> P"
      with X Y have "X = Xnew \<and> Y = Xnew" by fast
      then have "X = Y" by simp
      moreover have "X \<inter> Y \<noteq> {}" using eq_class_old eq_class_sub
        by (metis FalseFalse `X = Xnew \<and> Y = Xnew` inf_idem subset_empty)
      ultimately show ?thesis by simp
    qed
  }   
  then show ?thesis unfolding is_partition_def by force
qed
*)


(*
abbreviation "uniformTieBreaking random N G bids == 
Union \<circ> (argmax (setsum (resolvingBid' N G bids (nat random))))"
(* Union here acts as the_elem: picking the element of a singleton (i.e., stripping away the braces from {x}) *)
abbreviation "uniformTieBreaking2 random N G bids == 
% X. \<Union> (argmax (setsum (resolvingBid' N G bids (nat random))) X)"
abbreviation "Fun_upd X g == (%f x. if x \<in> X then (g x) else f x)"
notation Fun_upd (infix ":==" 80)
*)
(* lemma "possibleAllocationsRel N {} \<supseteq> {{}}" using lm31 lm28b emptyset_part_emptyset3 mm51 
mem_Collect_eq subsetI vimage_def *)


(*
lemma assumes "{} \<notin> Range a2" "{} \<notin> Range a1" "xx \<in> Domain a2 - (Domain a1)" shows 
"{(x, {y})| x y. y \<in> a1,,x & x \<in> Domain a1} \<noteq>
{(x, {y})| x y. y \<in> a2,,x & x \<in> Domain a2}" using assms 
                       
lemma assumes "a1 \<noteq> a2" "runiq a1" "runiq a2" shows "pseudoAllocation a1 \<noteq> pseudoAllocation a2" 
using assms mm55f inj_on_def runiq_def mm55h 

corollary assumes "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
"finite G" shows
"setsum (maxbid' a N G) (pseudoAllocation a) - setsum (maxbid' a N G) (pseudoAllocation aa) = 0 
= (a=aa)" 
*)

(* lemma assumes "a \<subseteq> N \<times> (Pow G - {{}})" shows 
"LinearCompletion bids N G || a \<supseteq> (partialCompletionOf bids) ` a" 
using assms restrict_def by fast *)

(*
lemma "(image omega) ` UNIV \<subseteq> finestpart ` UNIV" 
lemma "inj_on pseudoAllocation UNIV" using assms mm32 mm75c 
lemma assumes "pseudoAllocation a1 = pseudoAllocation a2" "{} \<notin> Range a1" "{} \<notin> Range a2" 
shows "a1 \<subseteq> a2" using assms mm32 
lemma  assumes "{} \<notin> Range f" "runiq f" shows "is_partition (omega ` f)" using assms
rev_image_eqI snd_eq_Range assms runiq_def runiq_imp_uniq_right_comp surjective_pairing 
Int_absorb Times_empty insert_not_empty is_partition_def  inf_commute inf_sup_aci(1) 
*)


(* 
fun perm where 
"perm [] = {}" | "perm (x#l) = 
{(n::nat, insertRightOf x (perm l,,(n div size l)) (n mod (size l)))| n . fact (size l) < n & n <= fact (1 + (size l))}
+* (perm l)"
*)


(*
lemma nn13: 
"vcga' N G bids random = the_elem (terminatingAuctionRel (N\<union>{auctioneer}) G (toFullBid (set G) bids) random)"
by auto
*)


(*
lemma mm49d: assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
shows "int (setsum (maxbid' a N G) (pseudoAllocation a)) - int (setsum (maxbid' a N G) (pseudoAllocation aa)) = 
int (card G) - int (card (pseudoAllocation aa \<inter> (pseudoAllocation a)))" 
proof -
let ?p=pseudoAllocation let ?f=finestpart let ?m=maxbid' let ?B="?m a N G" 
have "?p aa \<subseteq> N \<times> ?f G" using assms mm73c by blast
then have "?p aa \<subseteq> ?p a \<union> (N \<times> ?f G)" by auto
moreover have "finite (?p aa)" using assms mm48 mm54 by blast
ultimately have "int (setsum ?B (?p a)) - int (setsum ?B (?p aa)) = int (card (?p a)) - card (?p aa \<inter> (?p a))"
using mm49c 
moreover have "... = int (card G) - card (?p aa \<inter> (?p a))" using assms mm48 (* by smt *)
ultimately show ?thesis by presburger
qed

corollary mm70: 
assumes "finite G" "a \<in> possibleAllocationsRel N G" "aa \<in> possibleAllocationsRel N G"
shows "real (setsum (linearCompletion' (maxbid' a N G) N G) a) - setsum (linearCompletion' (maxbid' a N G) N G) aa = 
real (card G) - real (card (pseudoAllocation aa \<inter> (pseudoAllocation a)))" (is "?L=?R") 
proof -
  let ?l=linearCompletion' let ?m=maxbid' let ?s=setsum let ?p=pseudoAllocation
  let ?b="real \<circ> (?m a N G)" 
  have "?s (?l ?b N G) a = ?s ?b (?p a) & ?s (?l ?b N G) aa = ?s ?b (?p aa)" using assms mm69 by blast
  moreover have "?R = ?s ?b (?p a) - (?s ?b (?p aa))" using assms mm49b 
  
  ultimately moreover have "... = ?L" 
  ultimately show ?thesis 
qed
*)



(*
corollary mm92b: assumes "N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N"  
shows "vcga' N G bids random = chosenAllocation' (N\<union>{auctioneer}) G (toFullBid (set G) bids) random" 
using assms mm92 nn13 

corollary mm92c: assumes "N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" shows 
"vcga' N G bids random \<in> winningAllocationsRel (N \<union> {auctioneer}) (set G) (toFullBid (set G) bids)" 
using assms mm92b mm82 

corollary nn14: assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" shows 
"Range (vcga' N G b r) partitions (set G)"
using assms mm92b mm82 lm47 lm03 
proof -
let ?p=possibleAllocationsRel let ?a="vcga' N G b r"
let ?w=winningAllocationsRel let ?B="toFullBid (set G) b"
have "?a \<in> ?w (N\<union>{auctioneer}) (set G) ?B" using assms mm92b mm82 lm47 lm03 by auto
moreover have "?w (N\<union>{auctioneer}) (set G) ?B \<subseteq> ?p (N\<union>{auctioneer}) (set G)" 
using assms mm92b mm82 lm47 lm03 by presburger
ultimately have "?a \<in> ?p (N\<union>{auctioneer}) (set G)" by fast
then show "Range ?a partitions (set G)" using lm47 by presburger
qed

lemma nn15: assumes "f,,,x \<noteq> {}" shows "x \<in> Domain f" using assms by fast
lemma nn15b: assumes "runiq f" "f,,,x \<noteq> {}" shows "f,,,x \<in> Range f" 
using assms nn15 lll82 by (metis eval_runiq_in_Range)

corollary lll81b: assumes "a \<in> possibleAllocationsRel N G" shows 
"runiq a & runiq (a\<inverse>) & (Range a) partitions G & Domain a \<subseteq> N" 
using assms  image_iff lll81 converse_converse by (metis lm47)

corollary lll81c: assumes "a \<in> winningAllocationsRel N G b" shows 
"runiq a & runiq (a\<inverse>) & (Range a) partitions G & Domain a \<subseteq> N" 
using assms lll81b by (metis (hide_lams, no_types) in_mono lm03)

lemma nn16: assumes "is_partition P"  
shows "(p1 \<in> P & p2 \<in> P & p1 \<inter> p2 \<noteq> {}) \<longrightarrow> p1 = p2" using assms is_partition_def by metis 

lemma nn17: assumes "runiq f" "runiq (f^-1)" "x1 \<in> Domain f" "x2 \<in> Domain f" "f,,x1 = f,,x2" shows "x1=x2"
using assms by (metis DomainE converse_iff l31)

abbreviation "evalRel3 R x == if (Range R\<in>Pow UNIV) then (\<Union> (R``{x})) else the_elem (R``{x})"
(*MC: does not solve my problem because the if condition automatically makes R have values of set type*)

theorem assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}"
"g \<in> ((vcga' N G b r),,,n1)" "g \<in> ((vcga' N G b r),,,n2)" shows "n1 = n2" 
using assms nn14 eval_rel_def 
proof -
let ?d=Domain let ?r=Range let ?a="vcga' N G b r" let ?P="Range ?a" 
let ?p1="?a,,,n1" let ?p2="?a,,,n2" have 
2: "n1 \<in> ?d ?a & n2\<in>?d ?a" using assms by fast moreover have 
0: "runiq ?a & runiq (?a^-1)" using assms lll81c mm92c by blast ultimately have 
3: "?p1=?a,,n1 & ?p2=?a,,n2" using lll82 by fast
have "is_partition ?P" using assms nn14 is_partition_of_def by blast
then have "(?p1 \<in> ?P & ?p2 \<in> ?P & ?p1 \<inter> ?p2 \<noteq> {}) \<longrightarrow> ?p1 = ?p2" using nn16 by blast
moreover have 
1: "?p1 \<in> ?r ?a & ?p2 \<in> ?r ?a" using nn15b assms 0 by fast
moreover have "?p1 \<inter> ?p2 \<noteq> {}" using assms by fast
ultimately have "?p1 = ?p2" by linarith
then show "n1 = n2" using 0 2 nn17 3 by fast
qed

lemma nn18: assumes "P partitions A" shows "\<Union> P = A \<and> is_partition P" using assms is_partition_of_def by metis

theorem nn20: assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}"
"g \<in> ((vcga' N G b r),,,m)" shows "g \<in> set G"
proof -
have "(Range (vcga' N G b r)) partitions (set G)" using assms nn14 by blast then have 
0: "\<Union> (Range (vcga' N G b r)) = set G" using nn18 by blast
have "runiq (vcga' N G b r) & runiq ((vcga' N G b r)^-1)" using assms lll81c mm92c by blast
then have "(vcga' N G b r),,,m \<in> Range (vcga' N G b r)" using assms nn15b by fast
thus ?thesis using 0 assms by blast 
qed

lemma nn19: "condition1 (toFullBid (set G) b) auctioneer" 

lemma "vcga'' N \<Omega> b random \<in> (singleoutside' (addedBidder N))`(maximalAllocations' N (set \<Omega>) b)"
using assms 

lemma nn21b: "(singleoutside' (addedBidder N))`(maximalAllocations' N (set \<Omega>) b) \<subseteq>
(singleoutside' (addedBidder N))`(allAllocations' N (set \<Omega>))" using assms
by force
lemma assumes "\<Union>
(
(argmax (setsum (randomBids N \<Omega> b r)) (maximalAllocations' N (set \<Omega>) b))) \<in>
(maximalAllocations' N (set \<Omega>) b)" 
shows "vcga'' N \<Omega> b r \<in> (singleoutside' (addedBidder N))`(allAllocations' (N) (set \<Omega>))"
using assms nn21b by fast

lemma assumes "n\<in>N" "n \<noteq> addedBidder N" shows 
"Outside' ({n,addedBidder N})`(allAllocations' N G) \<subseteq> 
(singleoutside' (addedBidder (N-{n})))`allAllocations' (N-{n}) G" 
using assms lm19 lm51 
lemma assumes "X \<noteq> {}" shows "the_elem X \<in> X" using assms 

lemma assumes
"vcga'' N \<Omega> b r \<in> (singleoutside' (addedBidder N))`(allAllocations' N (set \<Omega>))"
"N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" shows
"vcga'' N \<Omega> b r -- n \<in> (singleoutside' (addedBidder N))`(allAllocations' (N-{n}) (set \<Omega>))" 
using assms Outside_def lm19 nn21b lm51 


lemma lm61g: assumes "condition1 (toFullBid (set G) b) auctioneer" 
"auctioneer \<noteq> n" "finite N" "a \<in> winningAllocationsRel (N\<union>{auctioneer}) (set G) c"
shows "alpha' N (set G) b n >= setsum (toFullBid (set G) b) (a -- n)" using assms lm61b by blast
lemma assumes "N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N" "seller\<noteq>n" shows "vcgp' N G b r n >= 0" using assms lm61g nn19 mm92c 
proof -
let ?w=winningAllocationsRel let ?N="N\<union>{auctioneer}" let ?a="vcga' N G b r"
let ?b="toFullBid (set G) b"
have "?a \<in> ?w ?N (set G) ?b" using assms mm92c by blast
then have "alpha' N (set G) b n >= setsum ?b (?a -- n)" using assms lm61g nn19 by blast
thus ?thesis by linarith
qed
*)

lemma "Domain (LinearCompletion b N G) = N \<times> ((Pow G) - {{}})" by blast
lemma mm93: "terminatingAuctionRel N G bids random = (((argmax \<circ> setsum) (resolvingBid' N G bids random))
\<circ> ((argmax \<circ> setsum) bids)) (possibleAllocationsRel N (set G))" by auto

(*

theorem 
(* assumes 
"distinct G" "set G \<noteq> {}" "finite N"  
"n1 \<in> Domain (vcga' N G b r)" 
"n2 \<in> Domain (vcga' N G b r)" 
"n1 = n2" *)
shows "(vcga' N G b r),,n1 \<inter> (vcga' N G b r),,n2={}" using assms 
sorry

theorem counterexample_lm64c: assumes "a \<in> allocationsUniverse" 
"n1\<in> Domain a" "n2 \<in> Domain a"
shows "a,,,n1 \<inter> a,,,n2={}" sorry

lemma "(\<Sum>i\<in>A. \<Sum>j\<in>B. f i j) = (\<Sum>j\<in>B. \<Sum>i\<in>A. f i j)" 
sorry

lemma lm240: "converse ` (injections X Y) =
{R. Domain (converse R) = Y & Range (converse R) \<subseteq> X & runiq (converse R) & runiq (converse (converse R))}"
using injections_def converse_def image_def sorry

corollary "LinearCompletion (bidMaximizedBy a N G Elsee 0) N G =
LinearCompletion (toFunction (bidMaximizedBy a N G)) N G" using lm07 image_cong lm08 
sorry

corollary lm02b: 
assumes "x \<in> (N \<times> (Pow G - {{}}))" shows 
"tiebids a N G x=linearCompletion' b N G x" sorry

lemma "argmax (setsum (resolvingBid' N G bids random)) (argmax (setsum bids) (possibleAllocationsRel N (set G)))
=
argmax (setsum (resolvingBid N G bids random)) (argmax (setsum bids) (possibleAllocationsRel N (set G)))"
using assms sorry

theorem assumes "distinct G" "set G \<noteq> {}" "finite N"  
"n1 \<in> Domain (vcga N G b r)" "n2 \<in> Domain (vcga N G b r)" 
(*"n1 \<noteq> n2"*) 
shows "(vcga N G b r),,n1 \<inter> (vcga N G b r),,n2={}"
using assms sorry (* nitpick [timeout=10000, tac_timeout=45, dont_specialize, show_consts] *)

(*
abbreviation "a00 == hd(perm2 (takeAll (%x. x\<in> set (winningAllocationsAlg N00 (G00) (b00 Else 0))) (possibleAllocationsAlg3 N00 G00)) 1)"
 abbreviation "a00 == hd(perm2 (takeAll (%x. x\<in> maximalStrictAllocations (int`N00) (G00) (b00 Else 0)) 
(allStrictAllocations N00 G00)) 1)"*)
(*value "tiebids' a00 N00 (set G00) (1,{12})"
value "(maxbid a00 N00 (set G00)) (1,{12})"
value "maximalStrictAllocations' (int`N00) (set G00) (b00 Else 0)"
value "graph a00 (tiebids' a00 N00 (set G00))"*)

lemma lm55: "tiebids' a N G = toFunction (Tiebids a N G)" by simp

corollary mm70f: assumes "finite G" "(a::('a::linorder\<times>_)set) \<in> allStrictAllocations' N G" 
"aa \<in> allStrictAllocations' N G" "aa \<noteq> a" shows 
"setsum' (Tiebids a N G) aa < setsum' (Tiebids a N G) a" using assms mm70d
proof -
term a
let ?f'=Tiebids let ?f=tiebids' let ?s'=setsum' let ?s=setsum let ?g'="?f' a N G" let ?g="?f a N G" 
have "a \<subseteq> Domain ?g' & aa \<subseteq> Domain ?g'" using assms mm64 mm63c
proof -
  have "a \<subseteq> N \<times> (Pow G - {{}}) \<and> aa \<subseteq> N \<times> (Pow G - {{}})"
    using assms(2) assms(3) mm63c by blast
  thus "a \<subseteq> Domain (LinearCompletion (real \<circ> pseudoAllocation a <| (N \<times> finestpart G)) N G) \<and> aa \<subseteq> Domain (LinearCompletion (real \<circ> pseudoAllocation a <| (N \<times> finestpart G)) N G)"
    by fastforce
qed then have 
0: "a \<inter> Domain ?g'=a & aa \<inter> Domain ?g'=aa" by blast moreover have 
1: "finite a & finite aa" using assms by (metis mm44) moreover have 
2: "runiq ?g'"  by (rule mm62)
ultimately moreover have "?s (toFunction ?g') (a \<inter> (Domain ?g')) = ?s' ?g' a" using lm48d by fast
moreover have "?s (toFunction ?g') (aa \<inter> (Domain ?g')) = ?s' ?g' aa" using lm48d 1 2 by blast
ultimately have "?s ?g a = ?s' ?g' a & ?s ?g aa = ?s' ?g' aa" using lm55 by auto 
moreover have "?s ?g aa < ?s ?g a" using assms by (rule mm70d)
ultimately moreover have "?s ?g aa < ?s' ?g' a" by presburger
ultimately show ?thesis by presburger  
qed
*)


(*
corollary lm90[code_unfold]: 
  fixes X
  assumes "finite X"
  shows "all_partitions X = set (map set (all_partitions_alg X))"
    unfolding all_partitions_alg_def
  using assms by (metis all_partitions_paper_equiv_alg' sorted_list_of_set)
(* all_partitions internally works with a list representing a set
   (this allows us to use the recursive function all_partitions_list).
   For a general list we can only guarantee compliance once we establish distinctness. *)

lemma remove_singleton_eq_class_from_part:
  assumes singleton_eq_class: "{X} \<subseteq> P"
      and part: "is_partition P"
  shows "(P - {X}) \<inter> {Y \<union> X} = {}"
    using assms unfolding is_partition_def
    by (metis Diff_disjoint Diff_iff Int_absorb2 Int_insert_right_if0 Un_upper2 empty_Diff insert_subset subset_refl)
*)
(*
text {* If new elements are added to a set, for any partition @{term P} of the original set,
  we can obtain a partition @{term Q} of the enlarged set by adding the new elements as a new equivalence class,
  and each equivalence class in @{term P} is a subset of one equivalence class in @{term Q}. *}
lemma exists_partition_of_strictly_larger_set:
  assumes part: "P partitions A"
      and new: "B \<inter> A = {}"
      and non_empty: "B \<noteq> {}"
  shows "(P \<union> {B}) partitions (A \<union> B) \<and> (\<forall> X \<in> P . \<exists> Y \<in> P \<union> {B} . X \<subseteq> Y)"
proof
  show "(P \<union> {B}) partitions (A \<union> B)"
    unfolding is_partition_of_def is_partition_def
  proof
    from part have "\<Union> P = A" unfolding is_partition_of_def ..

    show "\<Union> (P \<union> {B}) = A \<union> B"
    proof -
      from part have "\<Union> P = A" unfolding is_partition_of_def ..
      then show ?thesis by auto
    qed
    show "\<forall> X \<in> P \<union> {B} . \<forall> Y \<in> P \<union> {B} . (X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y)"
    proof
      fix X assume X_class: "X \<in> P \<union> {B}"
      show "\<forall> Y \<in> P \<union> {B} . (X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y)" using assms Un_insert_right X_class 
      is_partition_def is_partition_of_def partition_extension1 sup_bot.right_neutral by (metis(no_types))
    qed
  qed
  show "\<forall> X \<in> P . \<exists> Y \<in> P \<union> {B} . X \<subseteq> Y"
  proof
    fix X assume "X \<in> P"
    then have "X \<in> P \<union> {B}" by (rule UnI1)
    then show "\<exists> Y \<in> P \<union> {B} . X \<subseteq> Y" by blast
  qed
qed

text {* If zero or more new elements are added to a set,
  one can obtain for any partition @{term P} of the original set
  a partition @{term Q} of the enlarged set such that each equivalence class in @{term P} is a 
  subset of one equivalence class in @{term Q}. *}
(* TODO CL: choose a more appropriate name *)
lemma exists_partition_of_larger_set:
  assumes part: "P partitions A"
      and new: "B \<inter> A = {}"
  shows "\<exists> Q . Q partitions (A \<union> B) \<and> (\<forall> X \<in> P . \<exists> Y \<in> Q . X \<subseteq> Y)"
proof cases
  assume "B = {}"
  with part have "P partitions (A \<union> B) \<and> (\<forall> X \<in> P . \<exists> Y \<in> P . X \<subseteq> Y)" unfolding is_partition_of_def by auto
  then show ?thesis by fast
next
  assume non_empty: "B \<noteq> {}"
  with part new have "(P \<union> {B}) partitions (A \<union> B) \<and> (\<forall> X \<in> P . \<exists> Y \<in> P \<union> {B} . X \<subseteq> Y)"
    by (rule exists_partition_of_strictly_larger_set)
  then show ?thesis by blast
qed
*)


end
