(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)



theory DynamicAuctionTerminating

imports

"DynamicAuctionCommon"
"~/afp/Coinductive/Coinductive_List"
"~/afp/Show/Show_Instances"
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

(* liveleness states whether the auction has terminated in the current round *)
abbreviation "liveliness B == (livelinessList B) ! (size ((livelinessList B)) - 1)"

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




(* pairWise applies an operator Op to two lists l and m pairwise and returns the corresponding
   results in a list, starting with 0 up to the point that one list runs out of elements. *)
abbreviation "pairWise Op l m == 
  [Op (l!i) (m!i). i <- [0..<min (size l) (size m)]]"

(* If l is the list of bids by a single agent, then deltaBids will determine the difference
   between consecutive bids. *)
abbreviation "deltaBids l ==  (pairWise (op -) (tl l) l)"

(* firstInvalidBidIndex0 tells the first round in which a bidder does not increase their 
   sufficiently in order to be an active participant. The bidder can after that no longer
   change their final bid. It return 0 for the empty list.*)
abbreviation "firstInvalidBidIndex0 step l == 
nat (1 + hd (filterpositions2 (%x. x<step) (deltaBids l)@[size l- (1::int)]))"

(* Same as above for non-empty lists, but returns 1 for empty list*)
abbreviation "firstInvalidBidIndex1 step l == 
1 + hd (filterpositions2 (%x. x<step) (deltaBids l)@[size l- (1::nat)])"

(* Given a flat list L containing the bids from all participants in temporal order 
(except for its head representing the number of participants), we compose the list containing 
for each participant his last valid bid. If only the first n participants have submitted a bid, 
the produced list will have n entries. 
Obtaining a list of lists which is then flattened through concat 
(as opposed to directly building the wanted list) permits to smoothly handle such a case, 
in which some participants have not bid yet. 
Note that to speak of a valid bid, you must have specified a minimal increase threshold.
In this simple case, we assume this is the same for each participant, but in principle it could 
be a list, so as to have different thresholds for different participants. *)
definition "lastValidBidVector step L = 
            concat [sublist (pickParticipantBids L i) 
                            {firstInvalidBidIndex0 step (pickParticipantBids L i) - 1}
                    . i <- [0..<hd L]]"

definition "thresholdMessage step l = 
            ''Current winner: '' @ 
            (Show.show (maxpositions (lastValidBidVector step l))) @  
            ''\<newline>'' @ 
            ''Next, input bid for round ''@Show.show(roundForNextBidder l)@
            '', participant '' @
            (Show.show(nextBidder l))"

definition "staticAuctionThreshold step = 
staticAuctionGeneric (thresholdMessage step)
                     (%z. (\<exists> i \<in> {0..<hd z}. firstInvalidBidIndex0 step (pickParticipantBids z i)
                                              \<ge>size (pickParticipantBids z i)))"

definition "dynamicAuctionThreshold step input output == 
            conditionalIterates (output o (staticAuctionThreshold step) o input) (True,[])"

definition "dynamicAuctionThresholdExported  (input :: _)  (output:: _) = 
            snd (output ( String.implode ''Starting\<newline>Input the number of bidders:'', True, []),
                 dynamicAuctionThreshold 2 input output)"



section{* Theorems on terminating dynamic auctions *}


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

(* For all indices smaller than the firstInvalidBidIndex1 the deltaBids entries are greater 
   than the step size. *)
corollary deltaBidValidity: 
  fixes   l::"int list" 
  assumes "m+1 < firstInvalidBidIndex1 step l"
  shows   "(deltaBids l)!m \<ge> step" using assms lm05
  by fastforce

(* Auxiliary lemma for the following corollary. *)
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

lemma firstInvalidBidIndexEquivalence: 
  assumes "l \<noteq> []" 
  shows "firstInvalidBidIndex0 step l = firstInvalidBidIndex1 step l"
proof -
  let ?n = "size l" 
  let ?l = "filterpositions2 (%x. x<step) (deltaBids l)" 
  have 
  0: "?n-(1::nat)=?n-(1::int)" 
        using assms One_nat_def eq_diff_eq length_tl list.collapse list.size(4) of_nat_1 of_nat_add 
        by (metis (mono_tags, hide_lams))
  then have "(?l@[?n-(1::nat)]) = (?l@[?n-(1::int)])" 
     using list.simps(8) list.simps(9) map_append by (metis (no_types, lifting))
  then have "hd (?l@[?n-(1::nat)]) = hd (?l@[?n-(1::int)])" 
     using 0 lm02 append_is_Nil_conv length_tl list.collapse list.sel(1) list.simps(9) not_Cons_self
     by (metis(lifting,no_types))
  thus ?thesis by linarith
qed


lemma minimalValidBidValueAuxiliary: 
  fixes l::"int list" 
  assumes "(i::nat) < min (firstInvalidBidIndex1 (step::nat) l) (size l)"
  shows "l!i \<ge> hd l + i * step"
proof -
  have "\<forall>x \<in> {0..<i}. step \<le> (deltaBids l)!x" using assms deltaBidValidity by auto
  then have "setsum (nth (deltaBids l)) {0..<i} \<ge> setsum (%x. int_of_nat step) {0..<i}" 
    using setsum_mono by (metis (erased, lifting) int_of_nat_def)
  moreover have "setsum (%x. int_of_nat step) {0..<i} = i*step" 
    using int_of_nat_def by (metis atLeast0LessThan card_lessThan of_nat_mult setsum_constant)
  ultimately have "setsum (nth (deltaBids l)) {0..<i} \<ge> i*step" by presburger
  moreover have "l!i = hd l + setsum (nth (deltaBids l)) {0..<i}" 
    using assms deltaBidsSumCancellation by auto
  ultimately have "l!i \<ge> hd l + i*step" by presburger
  thus ?thesis by (metis of_nat_mult)
qed

corollary minimalValidBidValue: 
  fixes l::"int list" 
  assumes "int_of_nat i < min (firstInvalidBidIndex1 (step::nat) l) (size l)"
  shows "l!i \<ge> hd l + i*step" 
  using assms minimalValidBidValueAuxiliary int_of_nat_def by force

corollary minimalValidBidValueVariant: 
  fixes l::"int list" 
  assumes "int_of_nat i < min (firstInvalidBidIndex1 (step::nat) l) (size l)"
  shows "l!i \<ge> hd l + int_of_nat (i*step)" 
proof -
  have f1: "\<And>x\<^sub>1. min (length (tl (x\<^sub>1\<Colon>int list))) (length x\<^sub>1) = length (tl x\<^sub>1)" 
    by (metis (no_types) sizeTail length_tl)
  hence "int i < int (min (1 + hd(filterpositions2 (\<lambda>R. R < int step) 
                                                   (tolist (\<lambda>R. tl l ! R - l ! R) (length (tl l)))
                                                    @ [length (tl l)]))
                          (length l))" 
    using assms int_of_nat_def by auto
  thus "hd l + int_of_nat (i * step) \<le> l ! i" 
    using f1 by (simp add: int_of_nat_def minimalValidBidValue of_nat_mult)
qed

corollary minimalValidBidValueVariant2:
  fixes l::"int list" 
  assumes "i < firstInvalidBidIndex0 (step::nat) l" 
  shows "l!i \<ge> hd l + int_of_nat(i*step)"
proof -
  have 
  1: "firstInvalidBidIndex0 step l \<le> size l" using firstInvalidBidIndexUpperBound by auto
  have "l\<noteq>[]" using assms 
    proof -
      have "\<And>x\<^sub>1. filterpositions2 x\<^sub>1 ([]\<Colon>int list) = []"
        using Nil_is_map_conv MiscTools.lm123 empty_iff list.sel_set(1) list.set(1) map_nth 
              set_upt subsetCE
        by (metis (no_types))
      thus "l \<noteq> []" using assms by force
    qed 
  then have 
  0: "firstInvalidBidIndex0 step l = firstInvalidBidIndex1 step l" 
    using firstInvalidBidIndexEquivalence by blast
  then have "firstInvalidBidIndex1 step l \<le> size l" 
    using firstInvalidBidIndexUpperBound 1 by presburger 
  then moreover have "i < min (firstInvalidBidIndex1 step l) (size l)" 
    using assms 0 by linarith
  ultimately have "int_of_nat i < ..." 
    by (metis (no_types, lifting) int_of_nat_def of_nat_less_iff) 
  then have "l!i \<ge> hd l + int_of_nat (i*step)" 
    by (rule minimalValidBidValueVariant) 
  then show ?thesis by simp
qed

(* Type property between int and nat *)
lemma lm08: 
  "int_of_nat (m*n)=m*int_of_nat n" 
  by (metis int_of_nat_def zmult_int)

lemma lm09: 
  assumes "(t::int)>0" "y\<ge>z*t" 
  shows "(z::int)\<le>y div t" 
  using assms Divides.pos_mod_bound mult.commute zmult_zless_mono2
  by (metis div_mult_self1_is_id neq_iff zdiv_mono1)

corollary indexBidBound: 
  fixes l::"int list" 
  assumes "(i::nat) < firstInvalidBidIndex0 (step::nat) l"  "step > 0" 
  shows "int_of_nat i \<le> (l!i - hd l) div (int_of_nat step) + (1::int)"
proof - 
  have "l!i - hd l \<ge> int_of_nat(i*step)" using assms(1) minimalValidBidValueVariant2 by force
  moreover have "int_of_nat(i*step) = int_of_nat i * int_of_nat step" 
    using lm08 int_of_nat_def by auto
  ultimately have "int_of_nat i \<le> (l!i - hd l) div (int_of_nat step)" 
    using assms(2) lm09 by (metis int_of_nat_def of_nat_0_less_iff)
  show "int_of_nat i \<le> (l!i - hd l) div (int_of_nat step) + (1::int)"
    by (metis Nat_Transfer.transfer_nat_int_function_closures(6) 
        `int_of_nat i \<le> (l ! i - hd l) div int_of_nat step` add.commute 
        le_add_same_cancel2 order_trans) 
qed

lemma divMonotonicity: 
  assumes "(k::int)>0" "(i::int) \<le> j" 
  shows "i div k \<le> j div k" 
  using assms by (metis zdiv_mono1)

theorem auctionTermination: 
  fixes l::"int list" 
  assumes "step > (0::nat)" "\<forall>i<size l. l!i \<le> M" "l \<noteq> []" 
  shows  "int_of_nat (firstInvalidBidIndex0 step l) \<le> (M - hd l) div (int_of_nat step) + (2::int)"
  (is "?L \<le> ?R + (2::int)")
proof - 
  have 
  0: "?R \<ge> 0" using assms(1,2,3) Divides.transfer_nat_int_function_closures(1) 
                    diff_right_mono diff_self hd_conv_nth int_of_nat_def 
                    length_greater_0_conv max.semilattice_strict_iff_order of_nat_0_less_iff 
              by metis
  let ?i = "firstInvalidBidIndex0 step l - 1"
  {
    assume "\<not> ?thesis" 
    then have 
    1: "?L > ?R+(2::int)" by linarith 
    then have "?L > 0" using 0 by linarith 
    then have 
    2: "?i < firstInvalidBidIndex0 step l" 
      using One_nat_def diff_less int_of_nat_def lessI neq0_conv of_nat_0 order_less_irrefl
      by (metis (no_types, lifting))
    moreover have "firstInvalidBidIndex0 step l \<le> size l" 
      using firstInvalidBidIndexUpperBound by auto ultimately have 
    3: "?i < size l" by linarith
    moreover have 
    4: "int_of_nat ?i > ?R+(1::int)" using 0 1 2 int_of_nat_def by auto
    moreover have "int_of_nat ?i \<le> (l! ?i - hd l) div (int_of_nat step)+(1::int)"
      using 2 assms(1) by (rule indexBidBound)
    moreover have "... \<le> ?R+(1::int)" 
      using assms(1,2) divMonotonicity int_of_nat_def 2 3 by simp
    ultimately have False using 4 by linarith
  }
  thus ?thesis by (rule HOL.ccontr)
qed

(* let l be a list of bids by one bidder. From the first invalid bid onwards the bid list will be
   changed to be constantly the last valid bid, e.g. with step being 1 and l being
   (1 2 3 4 3 5 6 7 8) the bids become invalid as soon as the bidder decreases their bid, hence
   the result of ammendedBidList in this case will be (1 2 3 4 4 4 4 4 4) *)
abbreviation "amendedBidList step l == 
  updateList l {firstInvalidBidIndex0 step l..<size l} (%x. l!(firstInvalidBidIndex0 step l - 1))"

lemma amendedBidListIdentity: 
  assumes "i < firstInvalidBidIndex0 step l" 
  shows "(amendedBidList step l)!i = l!i"
proof -
  have "firstInvalidBidIndex0 step l \<le> size l" 
    using firstInvalidBidIndexUpperBound by auto 
  then have "i<size l" using assms by linarith
  thus ?thesis using assms by force
qed

lemma amendedBidListConstancy:
  assumes "i \<in> {firstInvalidBidIndex0 step l ..< size l}" 
  shows  "(amendedBidList step l)!i = l!(firstInvalidBidIndex0 step l - 1)" 
  using assms by auto

lemma amendedBidListSize: 
  "size (amendedBidList step l)= size l" 
  by simp

lemma bidConsistency:
  fixes l::"int list" 
  assumes "l \<noteq> []" "i+1 < firstInvalidBidIndex0 step l" 
  shows "l!(i+1) - (l!i) \<ge> step"
proof -
  have "i+1 < firstInvalidBidIndex1 step l" 
   using assms firstInvalidBidIndexEquivalence by fastforce 
  then have 
  0: "step \<le> (deltaBids l)!i" by (rule deltaBidValidity)
  have "i <(firstInvalidBidIndex0 step l)-(1)" using assms by linarith
  moreover have "...\<le>size l-(1)" using firstInvalidBidIndexUpperBound diff_le_mono by blast
  ultimately have "i\<in>{0..<size l - (1)}" by force
  then show ?thesis using deltaBidsLemma 0 by fastforce
qed

lemma firstInvalidBidProperty: 
  fixes l::"int list" 
  assumes "N+1 = firstInvalidBidIndex0 step l" "N+1 < size l" 
  shows "l!(N+1)-(l!N)<step"
proof -
  let ?d = "deltaBids l" 
  let ?f = filterpositions2 
  let ?P="%x. x < step" 
  have 
  1: "N = hd (?f ?P ?d @ [size l - (1::int)])" using assms by linarith
  moreover have "N \<noteq> size l - (1::int)" using assms by fastforce
  ultimately moreover have 
  2: "?f ?P ?d \<noteq> []" by fastforce
  ultimately moreover have "N = hd(?f ?P ?d)" 
  proof -
    have f1: "\<And>x x\<^sub>3. x = [] \<or> map x\<^sub>3 x ! 0 = (x\<^sub>3 (hd x\<Colon>nat)\<Colon>int)" 
      by (metis (lifting) hd_conv_nth length_greater_0_conv nth_map)
    then have "map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l)) = [] \<or> 
              hd (map int (filterpositions2 (\<lambda>R. R < step) (deltaBids l))) = int N" 
      by (metis (lifting) 1 hd_append)
    thus "N = hd (filterpositions2 (\<lambda>x. x < step) (deltaBids l))" 
      using f1 by (metis (lifting) 2 hd_conv_nth list.disc_map_iff nat_int)
  qed
  ultimately have "N\<in>set (?f ?P ?d)" by auto 
  then have "?P (?d!N)" unfolding filterPositionEquivalence by force
  thus ?thesis 
    using deltaBidsLemma Suc_eq_plus1 add.commute assms(2) atLeastLessThan_iff diff_diff_left le0
          zero_less_diff 
    by (metis(no_types))
qed

(* l is a list of bids from a single bidder. stopAuctionAt checks whether the bidder has terminated
   bidding. This is the case iff the bid is the same as in the previous round.  *)
lemma stopAuctionAtAsSet: 
  "set (stopAuctionAt l) = {n\<in>{1..<size l}. l!n = (l!(n - 1))}"
  unfolding filterPositionEquivalence stopAuctionAt_def by auto

(* Auxiliary lemma for lemma stopsCharacterization *)
lemma lm10:
  "stops B = {n. \<forall>i\<in>Domain B. (n \<in> {1..<size (unzip2 (B,,i))} & 
                 (unzip2 (B,,i))!n = (unzip2 (B,,i))!(n - 1))}"
  using stops_def stopAuctionAtAsSet by fast

(* stops is the set of all rounds in which each bidder bids the same as in the previous round. 
   B is the bid matrix. *)
lemma stopsCharacterization: 
  "stops B = {n. \<forall>i\<in>Domain B. (n\<in>{1..<size (B,,i)} & 
                              snd ((B,,i)!n) = snd ((B,,i)!(n-(1))))}"
  unfolding lm10 by force

lemma updateListCharacterization: 
  "updateList l X f = [if (n \<in> X) then (f n) else (l!n). n <- [0..<size l]]"
  unfolding override_on_def by blast

lemma stopsMeansNotLively: 
  assumes "Suc n < size (livelinessList B)" "n \<in> stops B" 
  shows "(livelinessList B)!(Suc n) = False"
proof -
  have "n < length (replicate (duration B) True) - 0 \<and> 
       (0 + n \<in> stops B \<or> 0 + n \<notin> stops B \<and> \<not> replicate (duration B) True ! (0 + n))"
    using Suc_less_eq assms(1) assms(2) comm_monoid_add_class.add.left_neutral 
          length_Cons length_map length_upt livelinessList_def
    by (metis)
  hence "\<not> tolist (\<lambda>R. R \<notin> stops B \<and> (R \<notin> stops B \<longrightarrow> replicate (duration B) True ! R)) 
                  (length (replicate (duration B) True)) ! n"
    using nth_map_upt by auto
  have "(True # tolist (\<lambda>n. if n \<in> stops B then False else replicate (duration B) True ! n) 
                       (length (replicate (duration B) True))) ! Suc n = False"
     by (metis `\<not> tolist (\<lambda>R. R \<notin> stops B \<and> (R \<notin> stops B \<longrightarrow> replicate (duration B) True ! R))
                         (length (replicate (duration B) True)) ! n` nth_Cons_Suc)
  show ?thesis using livelinessList_def 
     by (metis (no_types, lifting) `n < length (replicate (duration B) True) - 0 \<and> 
           (0 + n \<in> stops B \<or> 0 + n \<notin> stops B \<and> \<not> replicate (duration B) True ! (0 + n))`
         add.commute assms(2) diff_zero length_replicate  monoid_add_class.add.right_neutral
         nth_Cons_Suc nth_map_upt override_on_def)
qed

end

