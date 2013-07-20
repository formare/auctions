theory c

imports Main
(* "~~/src/HOL/Imperative_HOL/ex/Sublist" *)

begin
(*
lemma 1: shows "(sublist [] {0..<1})@(sublist [] {1..< (length [])}) = 
(sublist [] {0..< (length l)})" by auto

lemma 2: fixes l assumes "length l > 0" shows "(sublist l {0..<1})@(sublist l {1..<(length l)})=
sublist l {0..<length l}" using sublist_split by (smt assms)

lemma listsplit: fixes l shows "(sublist l {0..<1})@(sublist l {1..<(length l)})=
l" using 1 2 by (metis length_greater_0_conv sublist_all')

lemma fixes l shows "l = sublist l {0..<(length l)}" by force

lemma hdsub: assumes "l \<noteq> []" shows "sublist l {0} = [hd l]" 
by (metis assms hd_conv_nth length_greater_0_conv sublist_single)

lemma fixes l shows "(hd l)#(map (nth l) (upt 1 (size l)))=l" 

*)

definition norepetitions 
::"'a list => bool"
where "norepetitions l \<longleftrightarrow> card (set l) = length l"

lemma fixes l shows "norepetitions l \<longleftrightarrow> (card (set l) \<ge> length l)" 
using norepetitions_def by (metis card_length le_antisym)

lemma noreptl: fixes l assumes "norepetitions l" shows "norepetitions (tl l)" 
using assms norepetitions_def by (metis card_distinct distinct_card distinct_tl) 

lemma norepdrop: fixes l n assumes "norepetitions l" shows "norepetitions (drop n l)" 
using assms norepetitions_def by (metis card_distinct distinct_card distinct_drop)

lemma fixes l assumes "l \<noteq> []" shows "l!0=hd l" using assms by (metis hd_conv_nth)

lemma cardsize: fixes x assumes "finite x"
shows "length (sorted_list_of_set x) = card x" 
using assms by 
(metis finite_list length_remdups_card_conv length_sort sorted_list_of_set_sort_remdups)

lemma setlistid: fixes x assumes "finite x"
shows "set (sorted_list_of_set x)=x" using assms by simp

lemma norepset: fixes x assumes "finite x" shows 
"norepetitions (sorted_list_of_set x)" 
using assms cardsize setlistid norepetitions_def by metis

lemma map_commutes: fixes f::"'a => 'b" 
fixes Q::"'b => bool" fixes xs::"'a list" shows
"[ f n . n <- xs, Q (f n)] = [x <- (map f xs). Q x]"
proof -
  fix f::"'a => 'b" fix Q
  let ?g="\<lambda>n. (if Q (f n) then [f n] else [])"
  let ?lh="%l . concat (map ?g l)" let ?rh="%l . filter Q (map f l)"
  let ?I="%m . (\<forall> l::('a list) . ((size l=m) \<longrightarrow> (?lh l = ?rh l)))"
  have 10: "?I 0" by force
  have 11: "\<forall> m::nat . ((?I m) \<longrightarrow> (?I (Suc m)))"
  proof 
    fix m::nat show "(?I m) \<longrightarrow> (?I (Suc m))" 
    proof
      assume 1: "?I m"
      show "?I (Suc m)" 
      proof -
        {
        fix L::"'a list"  let ?A="take 1 L" let ?a="hd L" let ?l="tl L"        
        assume "size L=Suc m" hence 2: "L=?a#?l \<and> L=[?a]@?l \<and> size ?l=m" 
by (metis Suc_neq_Zero append_Cons append_Nil append_Nil2 append_eq_conv_conj diff_Suc_1 length_0_conv length_tl take_Suc)
        hence 0: "concat (map ?g ?l) = filter Q (map f ?l)" using 1 by blast
        hence "(concat (map ?g (?a#?l))) = (?g ?a)@(concat (map ?g ?l))" by fastforce
        also have "...= (?g ?a)@(filter Q (map f ?l))" using 0 by force 
        also have "...= (filter Q [f ?a])@(filter Q (map f ?l))" by fastforce
        also have "...= (filter Q (map f [?a]))@(filter Q (map f ?l))" by force
        also have "...= (filter Q ((map f [?a])@(map f ?l)))" by fastforce
        also have "...= (filter Q (map f ([?a]@?l)))" by auto
        also have "...= ?rh L" using 2 by presburger
        finally have "?lh L = ?rh L" using 2 by metis
        }
        thus "?I (Suc m)" by fast
      qed
    qed
qed
{
fix k have "?I k"
proof (rule nat.induct)
  show "?I 0" using 10 by blast
next fix m assume "?I m" thus "?I (Suc m)" using 11 by blast
qed
}
hence "\<forall> m . (?I m)" by fast
hence 3: "\<forall> l . (?lh l) = (?rh l)" by blast
fix xs show "[ f n . n <- xs, Q (f n)] = [x <- (map f xs). Q x]" using 3 by blast
qed

(*
hence "\<forall> l . ([ f n . n <- l, Q (f n)] = [x <- (map f l). Q x])" by fast
hence "[ f n . n <- ([a]@l), Q (f n)]=filter Q (map f ([a]@l))" 
by (metis Cons_eq_appendI calculation eq_Nil_appendI)
 have "filter Q (map f ([a]@l)) =[x <- (map f ([a]@l)) . Q x]" by fastforce

  hence "size l=Suc m \<longrightarrow> concat (map (\<lambda>n. if Q (f n) then [f n] else []) l) 
= filter Q (map f l)" using filter_def map_def Suc_def concat_def sorry
(* by (metis filter_id_conv map_nth) *)
  have "map (op ! l) [0..<length l] = l" by (metis map_nth)
  hence  "[ l!n . n <- [0..<size l], True]=[x <- l. True]" by fastforce
  have 1: "[x <- l. P x] = filter P l" by fast
  have 2: "[ f n . n <- l]=map f l" by fast
  have "[ f n . n <- l, Q (f n)] = filter Q (map f l)" using 1 apply auto sorry
  have "concat (map (\<lambda>n. if Q (f n) then [f n] else []) l) = filter Q (map f l)"
  using 1 2  sorry
(* [ x . x <- (map f l), P x]" *)
end

notepad
begin
  fix f x   fix l::"'a list" fix m
  have "(0=size l) \<longrightarrow> concat (map (\<lambda>u. if P (l ! u) then [l ! u] else []) [0..<0]) = 
  filter P l" 
  using map_def filter_def concat_def by auto
  hence "(0=size l) \<longrightarrow> [l!n . n \<leftarrow> [0..<size l], P (l!n)] = [x. x \<leftarrow> l, P x]" 
  by fastforce
  fix a l1 l2
have "[ (l@[a])!n . n <- [0..<size l]@[size l ..< size l], P((l@[a])!n)]
= [ l!n . n <- [0..<size l], P(l!n)]@[ [a]!n . n <-[size l ..< size l], P([a]!n)]
" sorry
  have "size ([a]@l)= 1+(size l)" by simp
  hence 2: "[0..<1]@[1..<size ([a]@l)]=[0..<size ([a]@l)]" 
using upt_add_eq_append by (metis le_add1 plus_nat.add_0)
  have 0: "[[a]!n . n <- [0], P ([a]!n)] = 
[(l@[a])!n . n<- [size l..<size l +1], P ((l@[a])!n)]" by simp
  have 1: "[x. x \<leftarrow> l@[a], P x]=[x . x <- l, P x] @ [x. x \<leftarrow> [a], P x]" by fastforce
  also have "... = [ l!n . n <- [0..<size l], P(l!n)]@
[[a]!n . n <- [0], P([a]!n)]" sorry
  also have "...=[ l!n . n <- [0..<size l], P(l!n)]@
[(l@[a])!n . n <- [size l], P((l@[a])!n)]" using 0 by fastforce
  also have "...=[ (l@[a])!n . n <- [0..<size l], P((l@[a])!n)]@
[(l@[a])!n . n <- [size l], P((l@[a])!n)]" sorry
  also have "...= [ (l@[a])!n . n <- [0..<size l]@[size l], P((l@[a])!n)]" by auto
  also have "...= [ (l@[a])!n . n <- [0..<size (l@[a])], P((l@[a])!n)]" 
using 2 by fastforce
  hence "[x. x \<leftarrow> l@[a], P x]=[ (l@[a])!n . n <- [0..<size (l@[a])], P((l@[a])!n)]"
by (metis calculation)

  have 0: "[[a]!n . n <- [0..<1], P a ] = [x . x <- [a], P x]" by auto

  have 1: "[x. x \<leftarrow> a#l, P x]=[x . x <- [a], P x] @ [x. x \<leftarrow> l, P x]" by fastforce
  also have "... = [[a]!n . n <- [0..<1], P a ]@[x . x <-l, P x]" using 0 by force
  also have "... =  [[a]!n . n <- [0..<1], P a ]@[l!n . n <- [0..<size l], P (l!n)]"
  sorry
  also have "... =  [[a]!n . n <- [0..<1], P ([a]!n) ]@[l!n . n <- [0..<size l], P (l!n)]"
  by fastforce
(*  also have "... =  [([a]@l)!n . n <- [0..<1], P (([a]@l)!n) ]@
[([a]@l)!n . n <- [1..<size l+1], P (([a]@l)!n)]"
  sorry*)
   also have "... =  [([a])!n . n <- [0..<1], P (([a])!n) ]@
[(l)!n . n <- [0..<size (l)], P (l!n)]" sorry
  also have "... = [([a]@l)!n . n <- ([0..<1]@[1..<size ([a]@l)]), P (([a]@l)!n)]" 

  also have "... = [([a]@l)!n . n <- ([0..<size ([a]@l)]), P (([a]@l)!n)]"
  using 2 by presburger
  have "[x. x \<leftarrow> l1@l2, P x]=[x . x <- l1, P x] @ [x. x \<leftarrow> l2, P x]" by fastforce
  let ?lf="%z . [z!n . n <- [0..<size z], P (z!n)]" let ?rf="%z . [x. x <- z, P x]"
  let ?lh="[l!n . n \<leftarrow> [0..<size l], P (l!n)]" let ?lx="take 1 ?lh" let ?lX="drop 1 ?lh"
  let ?rh="[x. x <- l, P x]" let ?rx="hd ?rh" let ?rX="tl ?rh"
  let ?k="drop 1 l"

  have "?lh = ?lx @ (?lX)" using append_def by (metis append_take_drop_id)
(*  have "tl (?rf l) = ?rf (tl l)" apply auto sorry *)
  have "tl (concat (map (\<lambda>x. if P x then [x] else []) l)) =
    concat (map (\<lambda>x. if P x then [x] else []) (tl l))" sorry
fix n
  have "{x. n \<in> {0..<m} \<and> x=f n} = set [f n . n <- [0..<m]]" 
  have "\<And>x. x \<in> set l \<Longrightarrow> P x \<Longrightarrow> x = l ! n" sorry
  have  "{ l!n . x=l!n \<and> n\<in>{0..<size l} \<and> P (l!n)} = {x . x\<in>set l \<and> P x}" 
  apply auto sorry
  value "[x. x \<leftarrow> [], P x]"
end
*)

end

