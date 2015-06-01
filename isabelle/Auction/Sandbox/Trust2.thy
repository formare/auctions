theory Trust2

imports DynamicAuctionCommon
"~/afp/Coinductive/Coinductive_List"
begin

lemma lm37: assumes "Suc n<size l" shows "(l!n = l!(Suc n)) = (sameToMyLeft l)!(Suc n)" 
using assms unfolding sameToMyLeft_def by fastforce

lemma lm37b: assumes "Suc n<size l" shows "(l!n = l!(Suc n)) = (sameToMyLeft' l)!(Suc n)" 
using assms by force

lemma lm38: assumes "0<size l" shows "(sameToMyLeft' l) ! 0 = False & (sameToMyLeft' l) ! 0 = False" 
unfolding sameToMyLeft_def using assms by auto
lemma lm39: "size (sameToMyLeft l)=size l & size (sameToMyLeft' l)=size l" unfolding sameToMyLeft_def by simp
lemma lm40: assumes "i < size l" shows "(sameToMyLeft l) ! i = (sameToMyLeft' l) ! i"   
proof -
have "i=0 \<or> (EX j. (i=Suc j))" (* using list_decode.cases by (metis ) *) sorry
then show ?thesis using assms lm37 lm37b lm38 sorry
qed
(*  
lemma lm39b:"size (sameToMyLeft l)=size l & size (sameToMyLeft'' l)=size l" sorry
lemma lm40b: assumes "i < size l" shows "(sameToMyLeft l) ! i = (sameToMyLeft'' l) ! i" sorry
corollary lm41: "ALL i<size (sameToMyLeft l). sameToMyLeft l ! i = sameToMyLeft'' l ! i" using lm40b 
lm39b length_map nth_map by metis
lemma lm42: "sameToMyLeft l = sameToMyLeft'' l" using lm41 lm39b nth_equalityI sorry
*)

definition "message l = ''Current winner: '' @ 
(Show.show (maxpositions (pickRoundBids l (currentRound l)))) @ 
''Liveliness: '' @ Show.show(livelinessList (listToBidMatrix l)) @ ''\<newline>'' @ 
''Next, input bid for round ''@Show.show(roundForNextBidder l)@'', participant ''@(Show.show(nextBidder l))"
(*
value "int_of_string ''123''"
definition trusted where "trusted (output::(String.literal => _)) (input::(integer  => _)) = 
(output (String.implode ''zio''), input 0)"
*)

(*
definition "prova (input::(integer => String.literal)) 
(output::(String.literal => String.literal))
= (output (String.implode ''start''), (inf_llist (output o String.implode o
concat o (tolist (String.explode o input \<circ> integer_of_nat))
)))"
*)

definition "prova (input::(integer => String.literal)) (output::(String.literal => String.literal))
= inf_llist (output o id o input \<circ> integer_of_nat)"
(* MC: This approach ignores the argument given to input, giving a thinner wrapper.
I couldn't find a way to preserve the previous history of inputs, in this way, however.
Hence we use evaluateMe below.*)
(*
definition "evaluateMe (input::(String.literal list => String.literal list)) 
(output::(String.literal list \<times> String.literal => String.literal list))
= (output ([], String.implode ''Starting\<newline>Input the number of bidders:''), 
iterates (output o (%x. (x,String.implode (concat (map String.explode x)))) o input) [])"
*)

abbreviation "staticAuction == 
(%l. (String.implode(message (map nat_of_integer l)), 
l
(* ,(livelinessList (listToBidMatrix (map nat_of_integer l)))!(currentRound (map nat_of_integer l)) *)
)) o (%l. (tl l)@[hd l])"

abbreviation "dynamicAuction input output == 
iterates (output o staticAuction o input) []"

primcorec conditionalIterates 
(* :: "(('a list) \<Rightarrow> ('a list)) \<Rightarrow> ('a list)\<Rightarrow> ('a list) llist" *) 
where 
"conditionalIterates f x = (if (fst x) then 
(LCons x (conditionalIterates f (f x))) else (LCons x LNil))"
  
abbreviation "appendNewBid z == ((snd o snd) z) @ [(nat_of_integer o fst) z]"

value "appendNewBid (1::integer, True, [2])"

abbreviation "liveliness B == (livelinessList B) ! (size ((livelinessList B)) - (1))"
abbreviation "staticAuction2 z == (String.implode (message (appendNewBid z)),
liveliness (listToBidMatrix (appendNewBid z)), appendNewBid z)"

abbreviation "dynamicAuction2 input output == 
conditionalIterates (output o staticAuction2 o input) (True,[])"
abbreviation "myInput x == (( integer_of_nat o (%(n::nat). 11-n) o Suc o size o snd) x, x)"
definition "evaluateMe2 
(input :: _)
(output:: _) 
= snd (output (
String.implode ''Starting\<newline>Input the number of bidders:'', True, []),
dynamicAuction2 input output)"
 
definition "evaluateMe (input(*::(integer list => integer list)*)) 
(output(*::(_ => integer list)*))
= snd (output (String.implode ''Starting\<newline>Input the number of bidders:'', [])
, dynamicAuction input output)"
term evaluateMe
(*
definition "evaluateMe (input::(integer list => integer list)) 
(output::(integer list \<times> String.literal => integer list))
= (output ([], String.implode ''Starting\<newline>Input the number of bidders:''), 
iterates (output o 
(%x. (x,String.implode (concat (map (Show.show \<circ> int_of_integer) x)))) 
o (%l. (tl l) @ [hd l]) o input) [])"
*)
(* 
input and output will be the only manually written Scala functions 
(and will be passed as arguments to evaluateMe as the only action of the main method of our Scala wrapper ) 
- input will take a list as an argument, and grow it by the input (side effect) provided by the user.
- output will take a pair (list, message) as an argument, will return list without touching it, 
while printing message to the user (side effect).
Thus, iterating the combined function output o XXX o input (where XXX is the Isabelle function doing 
the ``real work''), evaluateMe will provide a dynamic auction execution.
The length of the list passed to XXX will be used to determine in which round we are.

Thus, the manually-written Scala code (to be appended to the Isabelle-generated lines) will be:
*)

(*
def untrustedInput(n:List[String]) : List[String] = {
	val x=readLine;
	return (x::n);
}

def untrustedOutput(x: (List[String], String)) : List[String] = {
	println(snd (x));
	return (fst (x));
}

def main(args: Array[String]) {
	val x=evaluateMe(untrustedInput, untrustedOutput);
}

*)

(*
It can't probably get thinner than this.
My ambition would be to handle everything besides input/output from inside Isabelle, including
conversion from strings (as from input) to numbers and viceversa (for output); 
this is definitely possible, but how realistic given our schedule?
We could momentarily choose to directly use Scala integers as input/output, 
which is less robust/flexible/elegant but simpler.
*)


abbreviation "pairWise Op l m == [Op (l!i) (m!i). i <- [0..<min (size l) (size m)]]"
lemma lm01: assumes "n\<in>{0..<min (size l) (size m)}" shows "(pairWise Op l m)!n = Op (l!n) (m!n)"
using assms by auto
abbreviation "deltaBids l == (pairWise (op -) (tl l) l)"

lemma lm02: "min (size (tl l)) (size l)=size l - (1::nat)" by simp

lemma lm03: assumes "n\<in>{0..<(size l) - 1}" shows 
"(deltaBids l)!n = (l!(Suc n)) - (l!n)" using assms lm02 length_tl nth_tl atLeastLessThan_iff 
diff_zero monoid_add_class.add.left_neutral nth_map_upt by (metis (erased, lifting))

lemma lm03b: fixes l::"int list" (* remove *) assumes "n\<in>{0..<(size l)- 1}" shows 
"(deltaBids l)!n = (l!(Suc n)) - (l!n)" using assms lm02 length_tl nth_tl atLeastLessThan_iff 
diff_zero monoid_add_class.add.left_neutral nth_map_upt by (metis (erased, lifting))

(* lemma fixes l::"'a::ab_group_add list" shows 
"(\<Sum>i = 0..<size l-(1::nat). nth l i) = listsum l" using assms sorry *)

lemma "listsum (map (nth l) [0..<size l]) = listsum l" by (metis map_nth)
value "deltaBids [0::int, 2, 78]"
lemma "setsum (nth l) {0..<size l} = listsum l" using assms by (metis listsum_setsum_nth)

lemma lm10: "setsum (nth (deltaBids l)) {0..<size l-(1)} = setsum (%i. (l!(Suc i) - l!i)) {0..<size l-(1)}"
using assms lm03 lm02 atLeastLessThan_iff diff_zero length_upt nth_map set_upt setsum.cong
by smt2

lemma lm10b: fixes l::"int list" (*remove*)
assumes "m\<le>size l - (1)" shows 
"setsum (nth (deltaBids l)) {0..<m} = setsum (%i. (l!(Suc i) - l!i)) {0..<m}"
using assms lm03 unfolding setsum.cong sorry

lemma lm04a: fixes l::"'a::ab_group_add list" shows 
"(\<Sum>i = 0..<size l-(1). nth l (Suc i) - nth l i) = nth l (size l-(1)) - nth l 0" 
using One_nat_def Suc_diff_1 atLeastLessThanSuc_atLeastAtMost atLeastLessThan_empty 
diff_Suc_Suc diff_is_0_eq' diff_self  length_0_conv length_upt lessI nat_less_le 
neq0_conv set_upt setsum.cong setsum.empty setsum_Suc_diff by smt2

lemma lm04c: fixes l::"'a::ab_group_add list" shows
"(\<Sum>i = 0..<m. l ! (Suc i) - l!i) = l!m - l!0" using 
atLeastLessThanSuc_atLeastAtMost atLeastLessThan_empty 
diff_self order_refl setsum_Suc_diff not0_implies_Suc le0 
by (metis(no_types))

corollary lm04b: fixes l::"int list" shows 
"(\<Sum>i = 0..<size l-(1). nth l (Suc i) - nth l i) = nth l (size l-(1)) - nth l 0"
using lm04a by blast

corollary lm12: fixes l::"'a::ab_group_add list" shows 
"setsum (nth (deltaBids l)) {0..<size l-(1)} = l!(size l - (1)) - l!0" 
using assms lm04a lm10 by (metis (no_types))

corollary  fixes l::"int list" (* remove *) assumes "i<size l" shows 
"setsum (nth (deltaBids l)) {0..<i} = l!i - l!0" 
proof -
  have "i \<le> length l - 1" using assms by linarith
  thus "setsum (op ! (deltaBids l)) {0..<i} = l ! i - l ! 0" by (metis (no_types) lm04c lm10b)
qed

corollary lm12c: fixes l::"int list" (* remove *) assumes "i<size l" shows 
"setsum (nth (deltaBids l)) {0..<i} = l!i - (hd l)" using assms  
drop_0 hd_drop_conv_nth  
lm04c lm10b
sorry

lemma lm06: "[n. n\<leftarrow>[0..<N], Q n] = [n\<leftarrow>[0..<N]. Q n]" by (induct N) auto 
corollary lm06b: "filterpositions2 P l = [n<-[0..<size l]. P (l!n)]" unfolding lm06 
filterpositions2_def by blast
lemma lm07: "sorted [n\<leftarrow>[0..<N]. Q n]" by (metis (full_types) map_ident sorted_filter sorted_upt)
corollary lm07b: "sorted (filterpositions2 P l)" using lm07 lm06 unfolding filterpositions2_def by presburger

corollary lm11: assumes "sorted l" "x \<ge> Max (set l)" shows "sorted (l@[x])" 
using assms(1,2) sorted_append dual_order.trans by fastforce

lemma lm08: assumes "m < Min A" "finite A" shows "m \<notin> A" using assms by (metis Min.boundedE equals0D not_less not_less_iff_gr_or_eq)

lemma lm13: assumes "sorted l" "set l \<noteq> {}" shows "Min (set l)=hd l" using assms sorted.cases
List.finite_set Min_in insert_iff le_neq_trans list.sel(1) lm08 set_simps(2)
set_empty by (metis(no_types)) 
(*
proof -
  have f1: "l \<noteq> []" using assms(2) by fastforce
  have "\<And>v. \<forall>w. \<exists>uu uua. (sorted w \<longrightarrow> w = [] \<or> (uu\<Colon>'a) # uua = w) \<and> (sorted w \<and> v \<in> set uua \<longrightarrow> w = [] \<or> uu \<le> v)" by (metis (no_types) sorted.cases)
  thus "Min (set l) = hd l" using f1 by (metis (no_types) List.finite_set Min_in assms(1) assms(2) insert_iff le_neq_trans list.sel(1) lm08 set_simps(2))
qed
*)

lemma (*lm09:*) assumes "set [n\<leftarrow>[0..<N]. P n] \<noteq> {}" "m<Min (set [n\<leftarrow>[0..<N]. P n])" shows "\<not> (P m)" 
using assms Min_in lm08 by fastforce

corollary (* lm09c:*) assumes "set [(n::nat)\<leftarrow>[0..<N]. P n] \<noteq> {}" "m<hd [n<-[0..<N]. P n]" shows "\<not> (P m)"
using assms lm07 lm13
List.finite_set Trust2.lm08 atLeastLessThan_iff dual_order.trans hd_in_set 
less_nat_zero_code 
mem_Collect_eq not_less not_less_iff_gr_or_eq set_empty set_filter set_upt
sorry

corollary lm09b: assumes "set (filterpositions2 P l) \<noteq> {}" "m<hd (filterpositions2 P l)" shows
"\<not> (P (l!m))" using assms lm06b 
lm07 lm13
List.finite_set Trust2.lm08 atLeastLessThan_iff dual_order.trans hd_in_set 
less_nat_zero_code 
mem_Collect_eq not_less not_less_iff_gr_or_eq set_empty set_filter set_upt
proof -
  (* assume a1: "\<forall>v0 v1 v2. SMT2.fun_app (SMT2.fun_app (uu v0) v1) (v2\<Colon>nat) = (v2 \<in> set v1 \<and> SMT2.fun_app v0 v2)"
  assume "\<forall>v0 v1 v2. SMT2.fun_app (SMT2.fun_app (uua v0) v1) v2 = (SMT2.fun_app v0 (v1 ! v2\<Colon>'a)\<Colon>bool)"*)
  have f2: "{uub \<in> set [0..<length l]. P (l ! uub)} = set (filterpositions2 P l)" by (simp add: lm06b)
  hence f3: "0 \<le> hd (filterpositions2 P l) \<and> hd (filterpositions2 P l) < length l" using assms 
by (metis (erased, lifting) atLeastLessThan_iff hd_in_set lm123 set_empty subsetCE)

  hence f4: "m \<le> length l" using assms(2) by linarith
  have f5: "\<forall>v0 v1. (\<not> (v0\<Colon>nat) < Min v1 \<or> infinite v1) \<or> v0 \<notin> v1" using Trust2.lm08 by blast
  have "m < Min {uub \<in> set [0..<length l]. P (l ! uub)}" using f2 by (metis (no_types) Trust2.lm07 Trust2.lm13 assms(1) assms(2) lm06b)
  hence "m \<notin> set [0..<length l] \<or> \<not> P (l ! m)" using f2 f5 by auto
  then show "\<not> P (l ! m)" using f3 f4 by (metis (no_types) assms(2) atLeastLessThan_iff less_nat_zero_code not_less not_less_iff_gr_or_eq set_upt)
qed


(*  lm09c by metis *)

lemma lm14: "filter P l = [x<-l. P x]" by blast

lemma lm25: "set (filterpositions2 P l) = {0..<size l} \<inter> (P o (nth l))-`{True}"
unfolding lm06b by force

lemma lm26: "distinct (filterpositions2 P l)" using lm06b distinct_filter distinct_upt by metis

corollary "(filterpositions2 P l) = sorted_list_of_set ({0..<size l} \<inter> (P o (nth l))-`{True})"
using lm25 lm26 lm07b sorted_list_of_set List.finite_set finite_sorted_distinct_unique by (metis (no_types))
find_consts "(nat => 'a) => 'a list"
lemma "map f l = tolist (f o (nth l)) (size l)" by (metis List.map.compositionality map_nth)
lemma assumes "\<forall>n \<in> {0..<N}. f n = g n" shows "tolist f N = tolist g N" using assms by force

(* lemma "[x<-l. P x] = map (nth l) [n<-[0..<size l]. P (nth l n)]" using nth_map map_nth structInduct sorry *) 

lemma lm15a: "(nth l)`(set ([n<-[0..<size l]. P (l!n)])) \<supseteq> {y\<in>set l. P y}"
using imageE image_eqI  map_nth mem_Collect_eq  set_filter set_map subsetI by smt2
lemma (*lm15:*) "(nth l)`(set ([n<-[0..<size l]. P (l!n)])) = (set l) \<inter> (P-`{True})" using lm15a by force

lemma lm16: assumes "P y" "y\<in>set l" shows "y \<in> (nth l)`(set (filterpositions2 P l))" 
using assms mem_Collect_eq set_filter atLeast0LessThan image_iff in_set_conv_nth 
lessThan_iff set_upt unfolding lm06b by (metis(no_types,lifting))

lemma lm17: assumes 
"m < hd (filterpositions2 (%x. x<step) (deltaBids (*step*) l)@[size l-(1)])"
shows "\<not> ((deltaBids l)!m < step)" 
proof -
let ?l="filterpositions2 (%x. x<step) (deltaBids l)"
have "?l=[] \<longrightarrow> (\<forall>x \<in> set (deltaBids l). \<not> (x<step))" 
using lm16 empty_iff list.simps(8) set_empty set_map by (metis(no_types,lifting))
moreover have "?l \<noteq> [] \<longrightarrow> ?thesis" using assms(1) lm09b empty_iff hd_append2 
list.sel_set(1) by (metis (mono_tags))
ultimately show ?thesis using assms by fastforce
qed

abbreviation "firstInvalidBidIndex' step l == 
1 + hd (filterpositions2 (%x. x<step) (deltaBids l)@[size l- (1::nat)])"

corollary lm17b: fixes l::"int list" assumes "m+1 < firstInvalidBidIndex' step l"
shows "(deltaBids l)!m \<ge> step" using assms lm17 by fastforce

abbreviation "firstInvalidBidIndex step l == 
nat (1 + hd (filterpositions2 (%x. x<step) (deltaBids (*step*) l)@[size l- (1::int)]))"

corollary lm02b: "size (deltaBids l) = size l - 1" 
using lm02 diff_zero length_map length_upt by (metis)

lemma lm20: 
"hd ((filterpositions2 (%x. x<step) (deltaBids l))@[size l - (1::int)]) 
\<in> {-1..(size l-(1::int))}" 
proof -
let ?d="deltaBids l" let ?l="filterpositions2 (%x. x<step) ?d"
{
  assume 0: "?l \<noteq> []" then have "hd ?l \<in> {0..<size ?d}" using 
  hd_in_set subsetCE by (metis (erased, lifting) lm123)  
  moreover have "hd (?l@[size l - (1::int)])=hd ?l" using 0 hd_append2
  Nil_is_map_conv list.collapse list.sel(1) list.simps(9)
proof -
  have f1: "\<forall>b_x x\<^sub>5. hd (map x\<^sub>5 b_x) = (x\<^sub>5 (hd b_x\<Colon>nat)\<Colon>int) \<or> [] = b_x" by (metis hd_Cons_tl list.sel(1) list.simps(9))
  have "filterpositions2 (\<lambda>uu. uu < step) (tolist (Meson.COMBS (Meson.COMBB op - (op ! (tl l))) (op ! l)) (min (length (tl l)) (length l))) \<noteq> []" by (metis "0") (* > 2 s, timed out *)
  hence "filterpositions2 (\<lambda>uu. uu < step) (tolist (Meson.COMBS (Meson.COMBB op - (op ! (tl l))) (op ! l)) (min (length (tl l)) (length l))) \<noteq> [] \<and> [] \<noteq> map int (filterpositions2 (\<lambda>uu. uu < step) (tolist (Meson.COMBS (Meson.COMBB op - (op ! (tl l))) (op ! l)) (min (length (tl l)) (length l))))" by fastforce
  hence "\<not> sp\<^sub>1\<^sub>2\<^sub>5 (hd (map int (filterpositions2 (\<lambda>uu. uu < step) (tolist (Meson.COMBS (Meson.COMBB op - (op ! (tl l))) (op ! l)) (min (length (tl l)) (length l)))))) \<and> filterpositions2 (\<lambda>uu. uu < step) (tolist (Meson.COMBS (Meson.COMBB op - (op ! (tl l))) (op ! l)) (min (length (tl l)) (length l))) \<noteq> []" by (metis hd_append2) (* > 2 s, timed out *)
  thus "hd (map int (filterpositions2 (\<lambda>x. x < step) (deltaBids l)) @ [int (length l) - 1]) = int (hd (filterpositions2 (\<lambda>x. x < step) (deltaBids l)))" using f1 
  by (metis (mono_tags, lifting) "0" hd_append2 list.disc_map_iff)
qed
  ultimately have "hd (?l@[size l -(1::int)]) \<in> {0..<size l-(1::nat)}" by fastforce 
  then have "hd (?l@[size l -(1::int)]) \<in> {0..<size l-(1::int)}" by auto
} then have 
1: "?l\<noteq>[] \<longrightarrow> hd (?l@[size l -(1::int)]) \<in> {0..<size l-(1::int)}" by blast
have "?l=[] \<longrightarrow> hd(?l@[size l - (1::int)])=size l - (1::int)" by force
moreover have "size l - (1::int) \<in> {-1..(size l - (1::int))}" 
by (metis atLeastAtMost_iff diff_0 diff_add_eq diff_minus_eq_add int_of_nat_def minus_diff_eq order_refl zle_iff_zadd)
ultimately show "hd(?l@[size l - (1::int)]) \<in> {-1..size l-(1::int)}" using 1 by fastforce
qed

lemma (*lm21:*) assumes "(a::int) \<in> {x..y}" shows "1+a \<in> {1+x..1+y}" using assms by (metis add_le_cancel_left atLeastAtMost_iff)

corollary lm20b: "1 + hd (filterpositions2 (%x. x<step) (deltaBids l)@[size l-(1::int)])\<in> 
{(0::int)..int(size l)}" using lm20 lm21 sorry

corollary lm23b: "firstInvalidBidIndex step l \<le> size l" using 
assms lm20b Set_Interval.transfer_nat_int_set_functions(1) by blast
corollary lm23: "firstInvalidBidIndex step l \<in> {0..size l}" using lm23b by force
 
corollary lm20c: "firstInvalidBidIndex step l \<in> nat` {(0::int)..int(size l)}" using lm20b by fast

lemma lm99: assumes "x=y" shows "hd x = hd y" using arg_cong assms 
by simp

lemma lm24: assumes "l\<noteq>[]" shows "firstInvalidBidIndex step l = firstInvalidBidIndex' step l" 
proof -
let ?n="size l" let ?l="filterpositions2 (%x. x<step) (deltaBids l)" have 
0: "?n-(1::nat)=?n-(1::int)" using assms One_nat_def eq_diff_eq length_tl list.collapse list.size(4) of_nat_1 of_nat_add by (metis (mono_tags, hide_lams) )
then have "(?l@[?n-(1::nat)]) = (?l@[?n-(1::int)])" using list.simps(8) 
list.simps(9) map_append by (metis (no_types, lifting))
then have "hd (?l@[?n-(1::nat)]) = hd (?l@[?n-(1::int)])" using 0 lm02 append_is_Nil_conv 
length_tl list.collapse list.sel(1) list.simps(9) not_Cons_self by (metis(lifting,no_types))
thus ?thesis by linarith
qed

lemma lm19: "int (nat i)=i = (i\<ge>0)" by simp

lemma lm22: fixes l::"int list" assumes "(i::nat) < min (firstInvalidBidIndex' (step::nat) l) (size l)"
shows "l!i \<ge> hd l + i*step" using assms 
proof -
have "\<forall>x \<in> {0..<i}. step \<le> (deltaBids l)!x" using assms lm17b by auto
then have "setsum (nth (deltaBids l)) {0..<i} \<ge> 
setsum (%x. int_of_nat step) {0..<i}" using setsum_mono by (metis (erased, lifting) int_of_nat_def)
moreover have "setsum (%x. int_of_nat step) {0..<i} = i*step" 
using int_of_nat_def by (metis atLeast0LessThan card_lessThan of_nat_mult setsum_constant)
ultimately have "setsum (nth (deltaBids l)) {0..<i} \<ge> i*step" by presburger
moreover have "l!i = hd l + setsum (nth (deltaBids l)) {0..<i}" using assms lm12c by auto
ultimately have "l!i \<ge> hd l + i*step" by presburger
thus ?thesis by (metis of_nat_mult)
qed

corollary lm22b: fixes l::"int list" assumes "int_of_nat i < min (firstInvalidBidIndex' (step::nat) l) (size l)"
shows "l!i \<ge> hd l + i*step" using assms lm22 int_of_nat_def by force

corollary lm22c: fixes l::"int list" assumes "int_of_nat i < min (firstInvalidBidIndex' (step::nat) l) (size l)"
shows "l!i \<ge> hd l + int_of_nat (i*step)" using assms lm22 int_of_nat_def of_nat_mult lm22b 
proof -
  have f1: "\<And>x\<^sub>1. min (length (tl (x\<^sub>1\<Colon>int list))) (length x\<^sub>1) = length (tl x\<^sub>1)" by (metis (no_types) lm02 length_tl)
  hence "int i < int (min (1 + hd (filterpositions2 (\<lambda>R. R < int step) (tolist (\<lambda>R. tl l ! R - l ! R) (length (tl l))) @ [length (tl l)])) (length l))" using assms int_of_nat_def by auto
  thus "hd l + int_of_nat (i * step) \<le> l ! i" using f1 by (simp add: int_of_nat_def lm22b of_nat_mult)
qed

corollary lm27:
fixes l::"int list" assumes "i < firstInvalidBidIndex (step::nat) l" shows "l!i \<ge> hd l + int_of_nat(i*step)"
proof -
have 1: "firstInvalidBidIndex step l \<le> size l" using lm23b by auto
have "l\<noteq>[]" using assms 
proof -
  have "\<And>x\<^sub>1. filterpositions2 x\<^sub>1 ([]\<Colon>int list) = []"
  using Nil_is_map_conv lm123 empty_iff list.sel_set(1) list.set(1) map_nth set_upt subsetCE
  by (metis (no_types))
  thus "l \<noteq> []" using assms by force
qed then have 
0: "firstInvalidBidIndex step l = firstInvalidBidIndex' step l" using lm24 by blast
then have "firstInvalidBidIndex' step l \<le> size l" using lm23b 1 by presburger then moreover have 
"i < min (firstInvalidBidIndex' step l) (size l)" using assms 0 by linarith
ultimately have "int_of_nat i < ..." using int_of_nat_def of_nat_less_iff by presburger
then have "l!i \<ge> hd l + int_of_nat (i*step)" by (rule lm22c) then show ?thesis by simp
qed

lemma lm28: "int_of_nat (m*n)=m*int_of_nat n" by (metis int_of_nat_def zmult_int)

lemma lm29: assumes "(t::int)>0" "y\<ge>z*t" shows "(z::int)\<le>y div t" using assms 
div_mult_self2_is_id zdiv_mono1
by (metis add_0_right dual_order.refl int_div_pos_eq mult.commute)

lemma (*lm29:*) assumes "(t::int)>0" "y\<ge>z*t" shows "(z::int)\<le>y div t + 1" using assms
Divides.pos_mod_bound div_add_self2 div_mod_equality2 mult.commute zmult_zless_mono2 
proof -
  have "\<forall>x1 x0 x2. ((x2\<Colon>int) div x0 \<le> x1 div x0) = (0 \<le> x1 div x0 + - 1 * (x2 div x0))" by linarith
  hence f1: "0 \<le> y div t + - 1 * (z * t div t)" using assms(1) assms(2) zdiv_mono1 by presburger
  have "t \<noteq> 0" using assms(1) by force
  hence "z * t div t = z" using div_mult_self2_is_id by blast
  thus "z \<le> y div t + 1" using f1 by linarith
qed

corollary lm30: fixes l::"int list" assumes "(i::nat) < firstInvalidBidIndex (step::nat) l" 
"step > 0" shows "int_of_nat i \<le> (l!i - hd l) div (int_of_nat step) + (1::int)"
proof - have "l!i - hd l \<ge> int_of_nat(i*step)" using assms(1) lm27 by force
moreover have "int_of_nat(i*step) = int_of_nat i * int_of_nat step" by (metis int_of_nat_def of_nat_mult)
ultimately show "int_of_nat i \<le> (l!i - hd l) div (int_of_nat step) + (1::int)" using assms(2) 
int_of_nat_def of_nat_0_less_iff lm29 add.commute comm_monoid_add_class.add.left_neutral 
diff_le_eq diff_self le_less zero_less_int_conv zle_diff1_eq by (metis(no_types))
qed

lemma lm32: assumes "(k::int)>0" "(i::int) \<le> j" shows "i div k \<le> j div k" using assms by (metis zdiv_mono1)

theorem auctionTermination: fixes l::"int list" assumes "step > (0::nat)" "\<forall>i<size l. l!i \<le> M" "l \<noteq> []" shows 
"int_of_nat (firstInvalidBidIndex step l) \<le> (M - hd l) div (int_of_nat step) + (2::int)"
(is "?L \<le> ?R + (2::int)")
proof - have 
1: "?R \<ge> 0" using assms(1,2,3)
Divides.transfer_nat_int_function_closures(1) diff_right_mono diff_self hd_conv_nth int_of_nat_def 
length_greater_0_conv max.semilattice_strict_iff_order of_nat_0_less_iff by (metis)
let ?i="firstInvalidBidIndex step l - 1"
{
  assume "\<not> ?thesis" then have 
  0: "?L > ?R+(2::int)" by linarith then have "?L > 0" using 1 by linarith then have 
  2: "?i < firstInvalidBidIndex step l" using
  One_nat_def diff_less int_of_nat_def lessI neq0_conv of_nat_0 order_less_irrefl
  by (metis (no_types, lifting))
  moreover have "firstInvalidBidIndex step l \<le> size l" using lm23b by auto ultimately have 
  3: "?i < size l" by linarith
  moreover have 
  4: "int_of_nat ?i > ?R+(1::int)" using 0 1 2 int_of_nat_def by auto
  moreover have "int_of_nat ?i \<le> (l! ?i - hd l) div (int_of_nat step)+(1::int)"
  using 2 assms(1) by (rule lm30)
  moreover have "... \<le> ?R+(1::int)" using assms(1,2) lm32 int_of_nat_def 2 3 by simp
  ultimately have False using 4 by linarith
}
thus ?thesis by (rule HOL.ccontr)
qed

abbreviation "amendedbidlist3 step l == 
updateList l {firstInvalidBidIndex step l..<size l} (%x. l!(firstInvalidBidIndex step l - 1))"

corollary lm34: assumes "i<size l" shows 
"(i \<notin> A \<longrightarrow> (updateList l A f)!i = l!i) & (i \<in> A \<longrightarrow> (updateList l A f)!i = f i)" using assms by auto

theorem assumes "i<firstInvalidBidIndex step l" shows "(amendedbidlist3 step l)!i = l!i"
proof -
have "firstInvalidBidIndex step l \<le> size l" using lm23b by auto then have "i<size l" using assms by linarith
thus ?thesis using assms by force
qed

theorem assumes "i\<in>{firstInvalidBidIndex step l ..< size l}" shows 
"(amendedbidlist3 step l)!i = l!(firstInvalidBidIndex step l - 1)" using assms by auto

lemma lm36: "size (amendedbidlist3 step l)= size l" by simp

theorem lm35: fixes l::"int list" assumes "l \<noteq> []" "i+1 < firstInvalidBidIndex step l" 
shows "l!(i+1) - (l!i) \<ge> step"
proof -
have "i+1 < firstInvalidBidIndex' step l" using assms lm24 by fastforce then have 
0: "step \<le> (deltaBids l)!i" by (rule lm17b)
have "i <(firstInvalidBidIndex step l)-(1)" using assms by linarith
moreover have "...\<le>size l-(1)" using lm23b using diff_le_mono by blast
ultimately have "i\<in>{0..<size l - (1)}" by force
then show ?thesis using lm03 0 by fastforce
qed

theorem lm33: fixes l::"int list" assumes "N+1=firstInvalidBidIndex step l" 
"N+1<size l" shows "l!(N+1)-(l!N)<step" using assms lm25   
proof -
let ?d="deltaBids l" let ?f=filterpositions2 let ?P="%x. x<step" 
have 
3: "N=hd (?f ?P ?d @ [size l - (1::int)])" using assms by linarith
moreover have 
1: "N \<noteq> size l - (1::int)" using assms by fastforce
ultimately moreover have 
0: "?f ?P ?d \<noteq> []" by fastforce ultimately 
moreover have 
2: "N=hd(?f ?P ?d)" 
proof -
  have f1: "\<And>x x\<^sub>3. x = [] \<or> map x\<^sub>3 x ! 0 = (x\<^sub>3 (hd x\<Colon>nat)\<Colon>int)" 
  by (metis (lifting) hd_conv_nth length_greater_0_conv nth_map)
  then have "map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l)) = [] \<or> hd (map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l))) = int N" 
  by (metis (lifting) 3 hd_append)
  thus "N = hd (filterpositions2 (\<lambda>x. x < step) (deltaBids l))" using 
  f1 by (metis (lifting) 0 hd_conv_nth list.disc_map_iff nat_int)
qed
ultimately have "N\<in>set (?f ?P ?d)" by auto then have "?P (?d!N)" unfolding lm25 by force
thus ?thesis using lm03 Suc_eq_plus1 add.commute assms(2) atLeastLessThan_iff diff_diff_left 
le0 zero_less_diff by (metis(no_types))
qed

lemma assumes "step \<ge>(1::nat)" "firstInvalidBidIndex step (l::nat list)=Suc 0" shows "l!0 \<ge> 0*step" using assms by presburger

abbreviation "EX02 == [0::nat, 2, 4, 6, 8, 11, 12, 15]"

(* abbreviation "allowedBids bidSet bid == " activity rule*)

(*
lemma lm09: assumes "set l \<noteq> {}" "sorted l" "x \<ge> Max (set l)" "finite (set l)" shows "sorted (l@[x])" 
using assms sorted_append sorted_single Max.bounded_iff ball_empty list.set(1) set_ConsD by (metis (mono_tags, lifting) )
corollary lm09c: assumes "set l \<noteq> {}" "sorted l" "x \<ge> Sup (set l)" shows "sorted (l@[x])"
using assms lm09 Max_Sup List.finite_set
sorry
using assms lm09 sorted_single append_Nil set_empty2 List.finite_set Max_Sup sorry
*)


abbreviation "sublistAccordingTo list boolList == sublist list (set (filterpositions2 (%x. x=True) boolList))"

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
unfolding sameToMyLeft_def lm06b sorry 
lemma lm43: "set (stopAuctionAt l) = {n\<in>{1..<size l}. l!n = (l!(n-(1)))}"
unfolding lm06b sameToMyLeft_def stopAuctionAt_def by auto
lemma lm43b: "set (stopAuctionAt l) = {n. n\<in>{1..<size l} & l!n = (l!(n-(1)))}"
using lm43 by auto

lemma lm44: "stops B = {n. \<forall>i\<in>Domain B. (n\<in>{1..<size (unzip2 (B,,i))} & (unzip2 (B,,i))!n=(unzip2 (B,,i))!(n-(1)))}"
using stops_def lm43 by fast
lemma lm44b: "stops B = {n. \<forall>i\<in>Domain B. (n\<in>{1..<size (B,,i)} & snd ((B,,i)!n)=snd ((B,,i)!(n-(1))))}"
unfolding lm44 by force
lemma lm45: "updateList l X f = [if (n \<in> X) then (f n) else (l!n). n <- [0..<size l]]"
unfolding override_on_def by blast
lemma "((nth (livelinessList B)) o Suc)-`{False}\<supseteq>{0..<size (livelinessList B)-(1)}\<inter>stops B" 
using assms lm34 lm44b livelinessList_def 
nth_Cons_Suc diff_Suc_1 
comp_def diff_zero length_Cons length_map length_upt 
IntE atLeastLessThan_iff singletonI subsetI vimageI
by smt2
lemma lm47: "size (updateList l f X)=size l" by simp
(*
lemma lm48: assumes "i<duration B" "\<not> ((mbc0 B)!i)" shows "i \<in> stops B" 
using assms List.nth_replicate length_replicate lm34 by (metis (no_types, lifting))

lemma lm49a: "{0..<duration B} \<inter> ((nth (mbc0 B))-`{False}) \<subseteq> stops B"
using assms lm45 lm48 by fastforce
lemma lm49b: "{0..<duration B} \<inter> stops B \<subseteq> ((nth (mbc0 B))-`{False})"
using lm45 by force
corollary "nth (mbc0 B)-`{False} \<inter> {0..<duration B} = {0..<duration B} \<inter> stops B"
using lm49a lm49b by blast
lemma "size (livelinessList B)=1+duration B" unfolding livelinessList_def by force
*)

(* nth_Cons_Suc diff_Suc_1
comp_def diff_zero length_Cons length_map length_upt 
IntE atLeastLessThan_iff singletonI subsetI vimageI *)

(* *)
lemma assumes "Suc n<size (livelinessList B)" "n \<in> stops B" shows "((nth (livelinessList B)) o Suc) n=False"
using livelinessList_def  assms(1,2)
Suc_lessE diff_Suc_1 lm34 lm44b
comp_def diff_zero length_Cons length_map length_upt  nth_Cons_Suc
by smt2
lemma lm46: assumes "Suc n<size (livelinessList B)" "n \<in> stops B" shows "(livelinessList B)!(Suc n)=False"
using livelinessList_def lm45 assms(1,2)
Suc_lessE diff_Suc_1 comm_monoid_add_class.add.left_neutral
length_Cons length_map length_upt nth_Cons_Suc nth_map_upt
by smt2
(*  Suc_less_eq comm_monoid_add_class.add.left_neutral length_Cons length_map 
length_upt nth_Cons_Suc nth_map_upt by smt2 *)
(*
proof -
  have "n < length (replicate (duration B) True) - 0 \<and> (0 + n \<in> stops B \<or> 0 + n \<notin> stops B \<and> \<not> replicate (duration B) True ! (0 + n))"
using Suc_less_eq assms(1) assms(2) comm_monoid_add_class.add.left_neutral 
length_Cons length_map length_upt livelinessList_def
  by (metis)
  hence "\<not> tolist (\<lambda>R. R \<notin> stops B \<and> (R \<notin> stops B \<longrightarrow> replicate (duration B) True ! R)) (length (replicate (duration B) True)) ! n"
  using nth_map_upt by auto
  thus "(True # tolist (\<lambda>n. if n \<in> stops B then False else replicate (duration B) True ! n) (length (replicate (duration B) True))) ! Suc n = False" by simp
qed
*)

value "(listToBidMatrix E01)"
value "size (livelinessList (listToBidMatrix E01))"
value "stops (listToBidMatrix E01)"

end

