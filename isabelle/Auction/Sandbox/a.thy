theory a

imports Main Random Random_Sequence
"../Maximum"
"../Maskin3"
"../CombinatorialVickreyAuction"
"~~/src/HOL/Library/Code_Target_Nat"
"~~/src/HOL/Library/Permutations"
(* "~~/src/HOL/Library/DAList" *)

begin

lemma "arg_max' f A \<subseteq> f -` {Max (f ` A)}"
using assms arg_max'_def Max_def image_def 
vimage_def 
by force

lemma m00: "arg_max' f A = A \<inter>{ x . f x = Max (f ` A) }"
using assms arg_max'_def Max_def image_def vimage_def
by auto

lemma "arg_max' f A = A \<inter> f -` {Max (f ` A)}"
using assms arg_max'_def Max_def image_def vimage_def
by force

value "arg_max' id {0::nat,2,3,1234}"

fun prova where "prova f X 0 = X" | "prova f X (Suc n) = f n (prova f X n)"

fun prova2 where "prova2 f 0 = UNIV" |"prova2 f (Suc n) = f n (prova2 f n)"

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

fun geniter where "geniter f 0 = f 0" | "geniter f (Suc n)=(f (Suc n)) o (geniter f n)"

abbreviation "pseudodecreasing X Y == card X - 1 \<le> card Y - 2"
(* We'll use this to model the behaviour {1,2,3} -> {1,2} -> {1} -> {1} -> {1} ... *)
notation pseudodecreasing (infix "<~" 75)

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

abbreviation "auction b t == geniter (%n. (t n) o (arg_max' (proceeds (b n))))"

lemma mm06: assumes "X <~ Y" "Y <~ Z" shows "X <~ Z" using assms by linarith

lemma assumes "finite Y" "X \<subseteq> Y" shows "card X - 1\<le> card Y - 1" using assms 
by (metis card_mono diff_le_mono)

lemma mm07: assumes "finite Y" "X \<subseteq> Y" "Y <~ Z" shows "X <~ Z" using assms card_mono diff_le_mono 
by (metis le_trans)

lemma mm07b: assumes "finite Z" "X <~ Y" "Y \<subseteq> Z" shows "X <~ Z" using assms card_mono diff_le_mono 
by (metis le_trans)

value "sublist [0::nat, 1, 2, 3] {0..<1}"
definition "insertRightOf x l n = sublist l {0..<1+n} @ [x] @ sublist l {n+1..< 1+size l}"
value "insertRightOf 44 [0::nat, 1, 2, 3] 2"
value "insertRightOf (44::nat) [] 0"
value "fact (12::nat)"

value "{0::nat ..<2}"

(* 
fun perm where 
"perm [] = {}" | "perm (x#l) = 
{(n::nat, insertRightOf x (perm l,,(n div size l)) (n mod (size l)))| n . fact (size l) < n & n <= fact (1 + (size l))}
+* (perm l)"
*)
term graph
value "(10::nat) div 6 "
fun perm::"'a list => (nat \<times> ('a list)) set" where 
"perm [] = {}" | "perm (x#l) = 
graph {fact (size l) ..< 1+fact (1 + (size l))}
(%n::nat. insertRightOf x (perm l,,(n div size l)) (n mod (size l)))
+* (perm l)"

value "perm [1::nat]``{1::nat}"
value "(id (1::nat := 3)) 4"

fun permL where (* associate to every n=1...(size l)! a unique permutation of l, 
parsing all and only the possible permutations (assuming distinct l)*)
"permL [] = (%n. [])"|
"permL (x#l) = (%n. 
if (fact (size l) < n & n <= fact (1 + (size l))) 
then
(insertRightOf x (permL l (n div size l)) (n mod (size l)))
else
(x # (permL l n))
)"

value "fact (5::nat)"

value "permL [0::nat,1,2,3,4,5] 79"
abbreviation "indexof l x == hd (filterpositions2 (%y. x=y) l)"
notation indexof (infix "!-`" 75)
value "[10::nat, 11, 12] !-` 12" 

abbreviation "one N G random index == 
(% g n. (permL (sorted_list_of_set N) (random (index g))) !-` n + (card N)^(index g))"

term "split (one {0::nat, 1} {10::nat, 11} id id)"

abbreviation "tieBreakBidsSingle N G random index == % n g. 
(permL (sorted_list_of_set N) (random (index g))) !-` n + (card N)^(index g)
" (* Gives, for each _single_ good, and each participant, a bid.
In such a way that the resulting proceeds are unique for each possible allocation
(as soon as index is injective)
*)

abbreviation "tieBreakBids N G random index == split (% n X.
setsum (tieBreakBidsSingle N G random index n) X
)"

value "proceeds (tieBreakBids {0::nat, 1} {10::nat,1} id id)"

abbreviation "tieBreaker N G random index == 
%X. arg_max' (proceeds (tieBreakBids N G random index))X "

lemma "!X. card (tieBreaker N G random index X) = 1" sorry

abbreviation "tieBreakerSeq N G random index== %n. (if (n=0) then (%X. tieBreaker N G random index X) else
id)"

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

