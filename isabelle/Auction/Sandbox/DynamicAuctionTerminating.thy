theory DynamicAuctionTerminating

imports

"DynamicAuctionCommon"
"~~/src/afp/Coinductive/Coinductive_List"
"~~/src/afp/Show/Show_Instances"
"~~/src/HOL/Library/Code_Numeral"
"~~/src/HOL/Library/Code_Char"

begin

section{* Terminating dynamic auction using conditionalIterates *}

(* conditionalIterates is similar to iterates but operates on pairs and continues to iterate if
   and only if the first element of the pair returned by f is True. Its type is
   "(('a list) \<Rightarrow> ('a list)) \<Rightarrow> ('a list)\<Rightarrow> ('a list) llist" 
   LCons and LNil are the equivalents of Cons and Nil for lazy lists.*)
primcorec conditionalIterates 
  where "conditionalIterates f x = 
         (if   (fst x) 
          then (LCons x (conditionalIterates f (f x))) 
          else (LCons x LNil))"

(* z is a pair consisting of the new bid value and a pair of a boolean (stating whether the
   auction has not terminated in the previous round) and the flat list of all bids.
   It appends the new bid to the end of the flat list of all bids and returns this. E.g.
   z0 == (5::integer, (True, [3::nat,1,2,3])) then appendNewBid z0 returns [3, 1, 2, 3, 5].
 *)
abbreviation "appendNewBid z == ((snd o snd) z) @ [(nat_of_integer o fst) z]"

(* liveleness states whether the auction has terminated in the current round *)
abbreviation "liveliness B == (livelinessList B) ! (size ((livelinessList B)) - (1))"

(* In the following we use a simple example of a static auction, which can be replaced by a more
   sophisticated one. Here it just prints the current state of the auction after each input bid. 
   The print is done by the messageAfterEachBid. For instance with 
   "z0 == (5::integer, (True, [3::nat,1,2,3]))
   staticAuction will put first the 5 to the end of the list and then return the message
   "(STR ''Current winner: [0]\<newline>Liveliness: [True, True, True]\<newline>Next, input bid for round 1,
           participant 1'', True, [3, 1, 2, 3, 5])" :: "String.literal \<times> bool \<times> nat list"
   which will be used in the Scala code."

   staticAuction return a triple consisting of the message, the liveliness boolean, and the
   flat list of all bids.
   *)
abbreviation "staticAuction z == 
   (String.implode (messageAfterEachBid (appendNewBid z)),
    liveliness (listToBidMatrix (appendNewBid z)), 
    appendNewBid z)"

(* A dynamic auction starts being alive (True) with the empty list (no bids done yet, []), taking
   an input, computing the result for the staticAuction, and returning an output. This is iterated
   as long as the liveliness condition is True. *)
abbreviation "dynamicAuction input output == 
   conditionalIterates (output o staticAuction o input) (True,[])"



section{* Theorems on terminating dynamic auctions *}

(* pairWise applies an operator Op to two lists l and m pairwise and returns the corresponding
   results in a list, starting with 0 up to the point that one list runs out of elements. *)
abbreviation "pairWise Op l m == 
  [Op (l!i) (m!i). i <- [0..<min (size l) (size m)]]"

(* If l is the list of bids by a single agent, then deltaBids will determine the difference
   between consecutive bids. *)
abbreviation "deltaBids l ==  (pairWise (op -) (tl l) l)"

lemma sizeTail: 
  "min (size (tl l)) (size l) = size l - (1::nat)" 
  by simp

lemma deltaBidsLemma: 
  fixes   l::"int list"
  assumes "n\<in>{0..<(size l) - 1}"
  shows   "(deltaBids l)!n = (l!(Suc n)) - (l!n)" 
  using assms sizeTail length_tl nth_tl atLeastLessThan_iff diff_zero
        monoid_add_class.add.left_neutral nth_map_upt 
  by (metis (erased, lifting))

lemma deltaBidsSumLemma: 
  fixes l::"int list"
  assumes "m \<le> size l - 1" 
  shows   "setsum (nth (deltaBids l)) {0..<m} = setsum (%i. (l!(Suc i) - l!i)) {0..<m}"
  using assms deltaBidsLemma unfolding setsum.cong by auto

lemma sumDifferenceCancellation: 
  fixes l::"'a::ab_group_add list" 
  shows "(\<Sum>i = 0..<m. l ! (Suc i) - l!i) = l!m - l!0" 
  using atLeastLessThanSuc_atLeastAtMost atLeastLessThan_empty diff_self order_refl 
        setsum_Suc_diff not0_implies_Suc le0 
  by (metis(no_types))


corollary deltaBidsSumCancellation: 
  fixes   l::"int list" 
  assumes "i < size l" 
  shows   "setsum (nth (deltaBids l)) {0..<i} = l!i - (hd l)" 
  using assms sumDifferenceCancellation drop_0 hd_drop_conv_nth
  by (metis (no_types) One_nat_def Suc_leI Suc_pred atLeast0LessThan atLeastLessThan_empty
      deltaBidsSumLemma empty_iff lessThan_iff linorder_not_le)

lemma listEquivalence: 
  "[n. n\<leftarrow>[0..<N], Q n] = [n\<leftarrow>[0..<N]. Q n]" 
  by (induct N) auto 

corollary filterPositionEquivalence: 
  "filterpositions2 P l = [n<-[0..<size l]. P (l!n)]" 
  unfolding listEquivalence filterpositions2_def by blast

lemma filterSortednessInvariance: 
  "sorted [n\<leftarrow>[0..<N]. Q n]" 
  by (metis (full_types) map_ident sorted_filter sorted_upt)

corollary filterSortedness: 
  "sorted (filterpositions2 P l)" 
  using filterSortednessInvariance listEquivalence unfolding filterpositions2_def 
  by presburger

lemma minimumProperty: 
  assumes "m < Min A" "finite A" 
  shows "m \<notin> A" 
  using assms by (metis Min.boundedE equals0D not_less not_less_iff_gr_or_eq)

lemma minSortedListIsFirstElement: 
  assumes "sorted l" "set l \<noteq> {}" 
  shows "Min (set l)=hd l" 
  using assms sorted.cases List.finite_set Min_in insert_iff le_neq_trans 
        list.sel(1) minimumProperty set_simps(2) set_empty 
  by (metis(no_types)) 

lemma lm01: 
  assumes "set [n\<leftarrow>[0..<N]. P n] \<noteq> {}" "m < Min (set [n\<leftarrow>[0..<N]. P n])" 
  shows   "\<not> (P m)" 
  using assms Min_in minimumProperty by fastforce

corollary lm02: 
  assumes "set [(n::nat)\<leftarrow>[0..<N]. P n] \<noteq> {}" "m<hd [n<-[0..<N]. P n]" 
  shows   "\<not> (P m)"
  using assms filterSortednessInvariance lm01 minSortedListIsFirstElement by metis

corollary minimumPropertyVariant: 
  assumes "set (filterpositions2 P l) \<noteq> {}" "m<hd (filterpositions2 P l)" 
  shows   "\<not> (P (l!m))" 
  using assms filterPositionEquivalence lm02 by metis

(* Auxiliary lemma for the following one *)
lemma lm03: 
  "(nth l)`(set ([n<-[0..<size l]. P (l!n)])) \<supseteq> {y\<in>set l. P y}"
  using imageE image_eqI  map_nth mem_Collect_eq  set_filter set_map subsetI
proof -
  have "\<And>x\<^sub>1 x b_x. set (map x\<^sub>1 [R\<leftarrow>b_x . x (x\<^sub>1 (R\<Colon>nat)\<Colon>'a)]) = set (filter x (map x\<^sub>1 b_x))" 
     by (simp add: Compr_image_eq)
  thus "{y \<in> set l. P y} \<subseteq> op ! l ` set [n\<leftarrow>[0..<length l] . P (l ! n)]" 
     by (metis (no_types) eq_iff list.set_map map_nth set_filter)
qed

(* note that ` is the application of a function to a set, here the (nth l) function. 
   The lemma is used in the following. *)
lemma lm04: 
  assumes "P y" "y \<in> set l" 
  shows "y \<in> (nth l)`(set (filterpositions2 P l))" 
proof -
  have "y \<in> set (filter P l)" 
    by (simp add: assms(1) assms(2))
  thus "y \<in> op ! l ` set (filterpositions2 P l)" 
    by (metis lm03 contra_subsetD filterPositionEquivalence set_filter)
qed

(* step is a number that encodes the minimal increase of a bid in a round for a bidder. *)
lemma lm05: 
  assumes "m < hd (filterpositions2 (%x. x < step) (deltaBids l)@[size l - 1])"
  shows "\<not> ((deltaBids l)!m < step)" 
proof -
  let ?l = "filterpositions2 (%x. x<step) (deltaBids l)"
  have "?l=[] \<longrightarrow> (\<forall>x \<in> set (deltaBids l). \<not> (x<step))" 
    using lm04 by (metis (poly_guards_query, lifting) empty_iff image_empty list.set(1))
  moreover have "?l \<noteq> [] \<longrightarrow> ?thesis" 
    using assms minimumPropertyVariant by (metis (mono_tags) empty_iff hd_append2 list.sel_set(1))
  ultimately show ?thesis 
    using assms by fastforce
qed

(* firstInvalidBidIndex0 tells the first round in which a bidder does not increase their 
   sufficiently in order to be an active participant. The bidder can after that no longer
   change their final bid. It return 0 for the empty list.*)
abbreviation "firstInvalidBidIndex0 step l == 
nat (1 + hd (filterpositions2 (%x. x<step) (deltaBids l)@[size l- (1::int)]))"

(* Same as above for non-empty lists, but returns 1 for empty list*)
abbreviation "firstInvalidBidIndex1 step l == 
1 + hd (filterpositions2 (%x. x<step) (deltaBids l)@[size l- (1::nat)])"

(* For all indices smaller than the firstInvalidBidIndex1 the deltaBids entries are greater 
   than the step size. *)
corollary deltaBidValidity: 
  fixes   l::"int list" 
  assumes "m+1 < firstInvalidBidIndex1 step l"
  shows   "(deltaBids l)!m \<ge> step" using assms lm05
  by fastforce

(***)

(* Auxiliary lemma for the following corolary. *)
lemma lm06: 
  "hd ((filterpositions2 (%x. x < step) (deltaBids l)) @ [size l-(1::int)]) \<in> 
   {-1..(size l-(1::int))}" 
proof -
  let ?d = "deltaBids l" 
  let ?l = "filterpositions2 (%x. x<step) ?d"
  {
    assume 
    0: "?l \<noteq> []" 
    then have "hd ?l \<in> {0..<size ?d}" 
      using hd_in_set subsetCE by (metis (erased, lifting) lm123)  
    moreover have "hd (?l@[size l - (1::int)])=hd ?l" 
      proof -
        have f1: "\<And>x\<^sub>1 a_x. hd (map x\<^sub>1 a_x) = (x\<^sub>1 (hd a_x\<Colon>nat)\<Colon>int) \<or> [] = a_x" 
          by (metis (no_types) list.collapse list.sel(1) list.simps(9))
        have "map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l)) \<noteq> []" 
          by (metis "0" Nil_is_map_conv)
        hence "map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l)) \<noteq> [] \<and> 
               hd (map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l))) = 
               int (hd (filterpositions2 (\<lambda>R. R < step) (deltaBids l)))" 
          using f1 by (metis "0")
        thus "hd (map int (filterpositions2 (\<lambda>x. x < step) (deltaBids l)) @ [int (length l) - 1]) =
              int (hd (filterpositions2 (\<lambda>x. x < step) (deltaBids l)))" by simp
      qed
   ultimately have "hd (?l@[size l -(1::int)]) \<in> {0..<size l-(1::nat)}" by fastforce 
   then have "hd (?l@[size l -(1::int)]) \<in> {0..<size l-(1::int)}" by auto
  } 
  then have 
  1: "?l\<noteq>[] \<longrightarrow> hd (?l@[size l -(1::int)]) \<in> {0..<size l-(1::int)}" by blast
  have "?l=[] \<longrightarrow> hd(?l@[size l - (1::int)])=size l - (1::int)" by force
  moreover have "size l - (1::int) \<in> {-1..(size l - (1::int))}" 
    by (metis atLeastAtMost_iff diff_0 diff_add_eq diff_minus_eq_add int_of_nat_def 
        minus_diff_eq order_refl zle_iff_zadd)
   ultimately show "hd(?l@[size l - (1::int)]) \<in> {-1..size l-(1::int)}" using 1 by fastforce
qed

(* Auxiliary lemma for the following corollary. *) 
lemma lm07: 
  assumes "(a::int) \<in> {x..y}" 
  shows "1+a \<in> {1+x..1+y}" 
  using assms by (metis add_le_cancel_left atLeastAtMost_iff)

(* The first invalid bid index is in the range (0.. (size l). *)
corollary firstInvalidBidIndexRange: 
  "1 + hd (filterpositions2 (%x. x<step) (deltaBids l)@[size l-(1::int)]) \<in> 
   {(0::int)..int(size l)}" 
  using lm06 lm07 by fastforce

(* Reformulation of the above lemma firstInvalidBidIndexRange. *)
corollary firstInvalidBidIndexUpperBound:"firstInvalidBidIndex0 step l \<le> size l" using 
firstInvalidBidIndexRange Set_Interval.transfer_nat_int_set_functions(1) by blast

lemma lm24: 
  assumes "l \<noteq> []" 
  shows "firstInvalidBidIndex0 step l = firstInvalidBidIndex1 step l"
proof -
  let ?n = "size l" 
  let ?l = "filterpositions2 (%x. x<step) (deltaBids l)"
  have 1: "?n-(1::nat) = ?n-(1::int)" 
    using assms One_nat_def eq_diff_eq length_tl list.collapse list.size(4) of_nat_1 of_nat_add 
    by (metis (mono_tags, hide_lams) )
  then have 2: "?l@[?n-(1::nat)] = ?l@[?n-(1::int)]"
    proof -
      have "map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l)) @ [int (length l - 1)] = 
            map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l) @ [length l - 1])" by simp
      thus "map int (filterpositions2 (\<lambda>x. x < step) (deltaBids l) @ [length l - 1]) = 
            map int (filterpositions2 (\<lambda>x. x < step) (deltaBids l)) @ [int (length l) - 1]" 
        by (metis "1") 
   qed
  then have "hd (?l@[?n-(1::nat)]) = hd (?l@[?n-(1::int)])" 
    using 2 arg_cong 
    by (metis append_Cons list.collapse list.simps(9) nth_Cons_0 self_append_conv2)
  thus ?thesis by linarith
qed

lemma lm19: "int (nat i)=i = (i\<ge>0)" by simp


lemma lm22: fixes l::"int list" assumes "(i::nat) < min (firstInvalidBidIndex1 (step::nat) l) (size l)"
shows "l!i \<ge> hd l + i*step" using assms 
proof -
have "\<forall>x \<in> {0..<i}. step \<le> (deltaBids l)!x" using assms deltaBidValidity by auto
then have "setsum (nth (deltaBids l)) {0..<i} \<ge> 
setsum (%x. int_of_nat step) {0..<i}" using setsum_mono by (metis (erased, lifting) int_of_nat_def)
moreover have "setsum (%x. int_of_nat step) {0..<i} = i*step" 
using int_of_nat_def by (metis atLeast0LessThan card_lessThan of_nat_mult setsum_constant)
ultimately have "setsum (nth (deltaBids l)) {0..<i} \<ge> i*step" by presburger
moreover have "l!i = hd l + setsum (nth (deltaBids l)) {0..<i}" using assms deltaBidsSumCancellation by auto
ultimately have "l!i \<ge> hd l + i*step" by presburger
thus ?thesis by (metis of_nat_mult)
qed

corollary lm22b: fixes l::"int list" assumes "int_of_nat i < min (firstInvalidBidIndex1 (step::nat) l) (size l)"
shows "l!i \<ge> hd l + i*step" using assms lm22 int_of_nat_def by force

corollary lm22c: fixes l::"int list" assumes "int_of_nat i < min (firstInvalidBidIndex1 (step::nat) l) (size l)"
shows "l!i \<ge> hd l + int_of_nat (i*step)" using assms lm22 int_of_nat_def of_nat_mult lm22b
proof -
  have f1: "\<And>x\<^sub>1. min (length (tl (x\<^sub>1\<Colon>int list))) (length x\<^sub>1) = length (tl x\<^sub>1)" by (metis (no_types) sizeTail length_tl)
  hence "int i < int (min (1 + hd (filterpositions2 (\<lambda>R. R < int step) (tolist (\<lambda>R. tl l ! R - l ! R) (length (tl l))) @ [length (tl l)])) (length l))" using assms int_of_nat_def by auto
  thus "hd l + int_of_nat (i * step) \<le> l ! i" using f1 by (simp add: int_of_nat_def lm22b of_nat_mult)
qed

corollary lm27:
fixes l::"int list" assumes "i < firstInvalidBidIndex0 (step::nat) l" shows "l!i \<ge> hd l + int_of_nat(i*step)"
proof -
have 1: "firstInvalidBidIndex0 step l \<le> size l" using firstInvalidBidIndexUpperBound by auto
have "l\<noteq>[]" using assms 
proof -
  have "\<And>x\<^sub>1. filterpositions2 x\<^sub>1 ([]\<Colon>int list) = []"
  using Nil_is_map_conv lm123 empty_iff list.sel_set(1) list.set(1) map_nth set_upt subsetCE
  by (metis (no_types))
  thus "l \<noteq> []" using assms by force
qed then have 
0: "firstInvalidBidIndex0 step l = firstInvalidBidIndex1 step l" using lm24 by blast
then have "firstInvalidBidIndex1 step l \<le> size l" using firstInvalidBidIndexUpperBound 1 by presburger then moreover have 
"i < min (firstInvalidBidIndex1 step l) (size l)" using assms 0 by linarith
ultimately have "int_of_nat i < ..." by (smt2 int_of_nat_def of_nat_less_iff) 
then have "l!i \<ge> hd l + int_of_nat (i*step)" by (rule lm22c) then show ?thesis by simp
qed

lemma lm28: "int_of_nat (m*n)=m*int_of_nat n" by (metis int_of_nat_def zmult_int)

lemma lm29: assumes "(t::int)>0" "y\<ge>z*t" shows "(z::int)\<le>y div t + 1" using assms
Divides.pos_mod_bound div_add_self2 div_mod_equality2 mult.commute zmult_zless_mono2 by smt2

corollary lm30: fixes l::"int list" assumes "(i::nat) < firstInvalidBidIndex0 (step::nat) l" 
"step > 0" shows "int_of_nat i \<le> (l!i - hd l) div (int_of_nat step) + (1::int)"
proof - have "l!i - hd l \<ge> int_of_nat(i*step)" using assms(1) lm27 by force
moreover have "int_of_nat(i*step) = int_of_nat i * int_of_nat step" using lm28 int_of_nat_def by auto
ultimately show "int_of_nat i \<le> (l!i - hd l) div (int_of_nat step) + (1::int)" using assms(2) lm29 by (metis int_of_nat_def of_nat_0_less_iff)
qed

lemma lm32: assumes "(k::int)>0" "(i::int) \<le> j" shows "i div k \<le> j div k" using assms by (metis zdiv_mono1)

theorem auctionTermination: fixes l::"int list" assumes "step > (0::nat)" "\<forall>i<size l. l!i \<le> M" "l \<noteq> []" shows 
"int_of_nat (firstInvalidBidIndex0 step l) \<le> (M - hd l) div (int_of_nat step) + (2::int)"
(is "?L \<le> ?R + (2::int)")
proof - have 
1: "?R \<ge> 0" using assms(1,2,3)
Divides.transfer_nat_int_function_closures(1) diff_right_mono diff_self hd_conv_nth int_of_nat_def 
length_greater_0_conv max.semilattice_strict_iff_order of_nat_0_less_iff by metis
let ?i="firstInvalidBidIndex0 step l - 1"
{
  assume "\<not> ?thesis" then have 
  0: "?L > ?R+(2::int)" by linarith then have "?L > 0" using 1 by linarith then have 
  2: "?i < firstInvalidBidIndex0 step l" using
  One_nat_def diff_less int_of_nat_def lessI neq0_conv of_nat_0 order_less_irrefl
  by (metis (no_types, lifting))
  moreover have "firstInvalidBidIndex0 step l \<le> size l" using firstInvalidBidIndexUpperBound by auto ultimately have 
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
updateList l {firstInvalidBidIndex0 step l..<size l} (%x. l!(firstInvalidBidIndex0 step l - 1))"

corollary lm34: assumes "i<size l" shows 
"(i \<notin> A \<longrightarrow> (updateList l A f)!i = l!i) & (i \<in> A \<longrightarrow> (updateList l A f)!i = f i)" using assms by auto

theorem assumes "i<firstInvalidBidIndex0 step l" shows "(amendedbidlist3 step l)!i = l!i"
proof -
have "firstInvalidBidIndex0 step l \<le> size l" using firstInvalidBidIndexUpperBound by auto then have "i<size l" using assms by linarith
thus ?thesis using assms by force
qed

theorem assumes "i\<in>{firstInvalidBidIndex0 step l ..< size l}" shows 
"(amendedbidlist3 step l)!i = l!(firstInvalidBidIndex0 step l - 1)" using assms by auto

lemma lm36: "size (amendedbidlist3 step l)= size l" by simp

theorem lm35: fixes l::"int list" assumes "l \<noteq> []" "i+1 < firstInvalidBidIndex0 step l" 
shows "l!(i+1) - (l!i) \<ge> step"
proof -
have "i+1 < firstInvalidBidIndex1 step l" using assms lm24 by fastforce then have 
0: "step \<le> (deltaBids l)!i" by (rule deltaBidValidity)
have "i <(firstInvalidBidIndex0 step l)-(1)" using assms by linarith
moreover have "...\<le>size l-(1)" using firstInvalidBidIndexUpperBound using diff_le_mono by blast
ultimately have "i\<in>{0..<size l - (1)}" by force
then show ?thesis using deltaBidsLemma 0 by fastforce
qed

theorem lm33: fixes l::"int list" assumes "N+1=firstInvalidBidIndex0 step l" 
"N+1<size l" shows "l!(N+1)-(l!N)<step"
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
ultimately have "N\<in>set (?f ?P ?d)" by auto then have "?P (?d!N)" unfolding filterPositionEquivalence by force
thus ?thesis using deltaBidsLemma Suc_eq_plus1 add.commute assms(2) atLeastLessThan_iff diff_diff_left 
le0 zero_less_diff by (metis(no_types))
qed

lemma assumes "step \<ge>(1::nat)" "firstInvalidBidIndex0 step (l::nat list)=Suc 0" shows "l!0 \<ge> 0*step" using assms by presburger

abbreviation "EX02 == [0::nat, 2, 4, 6, 8, 11, 12, 15]"

(* abbreviation "allowedBids bidSet bid == " activity rule*)

(*
lemma minimumPropertyVariant: assumes "set l \<noteq> {}" "sorted l" "x \<ge> Max (set l)" "finite (set l)" shows "sorted (l@[x])" 
using assms sorted_append sorted_single Max.bounded_iff ball_empty list.set(1) set_ConsD by (metis (mono_tags, lifting) )
corollary minimumPropertyVariantc: assumes "set l \<noteq> {}" "sorted l" "x \<ge> Sup (set l)" shows "sorted (l@[x])"
using assms minimumPropertyVariant Max_Sup List.finite_set
sorry
using assms minimumPropertyVariant sorted_single append_Nil set_empty2 List.finite_set Max_Sup sorry
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
unfolding filterPositionEquivalence sorry 
lemma lm43: "set (stopAuctionAt l) = {n\<in>{1..<size l}. l!n = (l!(n-(1)))}"
unfolding filterPositionEquivalence stopAuctionAt_def by auto
lemma lm43b: "set (stopAuctionAt l) = {n. n\<in>{1..<size l} & l!n = (l!(n-(1)))}"
using lm43 by auto
term stops
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
(*lemma lm47: "size (updateList l f X)=size l" by simp
lemma lm48: assumes "i<duration B" "\<not> ((mbc0 B)!i)" shows "i \<in> stops B" 
using assms List.nth_replicate length_replicate lm34 by (metis (no_types, lifting))

lemma lm49a: "{0..<duration B} \<inter> ((nth (mbc0 B))-`{False}) \<subseteq> stops B"
using assms lm45 lm48 by fastforce
lemma lm49b: "{0..<duration B} \<inter> stops B \<subseteq> ((nth (mbc0 B))-`{False})"
using lm45 by force

corollary "nth (mbc0 B)-`{False} \<inter> {0..<duration B} = {0..<duration B} \<inter> stops B"
using lm49a lm49b by blast
*)
lemma "size (livelinessList B)=1+duration B" unfolding livelinessList_def by force

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

end

