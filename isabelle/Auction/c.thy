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

lemma norepdrop: fixes l n assumes "norepetitions l" shows "norepetitions (drop n l)" 
using assms norepetitions_def by (metis card_distinct distinct_card distinct_drop)

lemma fixes l assumes "l \<noteq> []" shows "l!0=hd l" using assms by (metis hd_conv_nth)
*)


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

