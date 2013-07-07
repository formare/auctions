theory b
imports Main a
begin

(*
(* Approach 1: Everything is a list *)
definition growpart 
::" 'a => 'a list list => 'a list => 'a list list"
where 
"growpart e X x = ( e # x ) # (removeAll x X)"

definition childrenofpartition (* given a partition p of X, obtain 
all the possible partitions of e#X being coarser than p*)
::" 'a => 'a list list => 'a list list list"
where 
"childrenofpartition e p =([e] # p ) # map (growpart e p) p"

definition partitionsconstructor 
::"'a => 'a list list list => 'a list list list "
where "partitionsconstructor e P = concat (map (childrenofpartition e) P)"

fun all_partitions ::" 'a list => 'a list list list"
where "all_partitions [] = [[]]"|
"all_partitions (e # X) = partitionsconstructor e (all_partitions X)"

definition all_partitions_set where (* Simplify all these [map, set] occurrences?*)
"all_partitions_set X = set (map set (map (map set) (all_partitions (sorted_list_of_set X))))"
*)

(* Approach 2: Everythin's a set, except the very initial input, which is a list (of elements)
because I don't know how to do recursive definitions on finite sets *)

definition growpart 
::"'a => ('a set \<times> ('a set set)) => 'a set set" 
where "growpart e x=snd x - {fst x} \<union> {fst x \<union> {e}}"

definition childrenofpartition 
::"'a => ('a set set) => ('a set set set)" 
where 
"childrenofpartition e p = insert (insert {e} p) ((growpart e) ` (p \<times> {p}))"

definition partitionsconstructor 
:: " 'a => 'a set set set => 'a set set set"
where "partitionsconstructor e P = 
\<Union> (childrenofpartition e ` P)"

fun allpartitionsoflist (* input is a list representing a set (see comment above), 
hence output from a list with repetitions is not guaranteed compliance *)
::"'a list => 'a set set set"
where 
"allpartitionsoflist []={{}}"|
"allpartitionsoflist (e # X) = partitionsconstructor e (allpartitionsoflist X)" 

definition allpartitions where "allpartitions X = allpartitionsoflist (sorted_list_of_set X)"

(* value "allpartitions {x}" *)

lemma l1: fixes e p assumes "is_partition p1" and "p2 \<in> (childrenofpartition e p1)"
shows "is_partition p2"
proof -
show ?thesis sorry
qed

definition parent where "parent e p = ((%x . x - {e}) ` p) - {{}}"

lemma l2: fixes e p assumes "is_partition p" shows 
"p \<in> childrenofpartition e (parent e p)" 
sorry

definition mypred
::" 'a  => nat => bool"
where "mypred x n=
(\<forall> X::('a list) . (length X=(n+1)) \<longrightarrow> 
(all_partitions_classical (set X) = allpartitionsoflist (X))
)"

lemma fixes x::"'a" fixes n assumes "mypred x n" shows "mypred x (Suc n)" 
proof -
fix x::"'a" fix n
assume 4: "mypred x n"
{
fix X1 X2 ::"('a list)" (* have "X2 = (hd X2) # X1" sorry *)
(*def X1 == "remove1 (hd X2) X2"*)
let ?l = "allpartitionsoflist" let ?c = "all_partitions_classical" let ?e = "hd X2"
(* what's the difference with def l == "allpartitionsoflist" (which doesn't work)?? *)
let ?f = "parent ?e" let ?ch = "childrenofpartition"
have 2: "X2=?e # X1" sorry 
assume "length X2=(Suc (n+1))" hence "length X1=n+1" (* by (metis Suc_length_conv X1_def hd.simps remove1.simps(2))*) sorry
hence 1: "?c (set X1) = ?l X1" using 4 mypred_def by fast
have "?c (set X2) \<subseteq> ?l X2"
proof 
  fix "p2" assume "p2 \<in> ?c (set X2)"
  have "is_partition p2" sorry 
  hence "p2 \<in> ?ch ?e (?f p2)" using l2 by fast
  hence 5: "{{p2}} \<subseteq> ?ch ?e ` {?f p2}" sledgehamm
  have "(?f p2) \<in> (?c (set X1))" sorry
  hence "?f p2 \<in> (?l X1)" using 1 by fast
  hence 3:" {?f p2} \<subseteq> (?l X1)" by fastforce
(*  hence "EX AA. AA \<subseteq> (?l X1) & ?ch ?e ` {?f p2} = ?ch ?e ` AA" by for *)
  hence "(?ch ?e ` ({?f p2})) \<subseteq> (?ch ?e `(?l X1))" using subset_image_iff by metis
  hence "{p2} \<subseteq> ?ch ?e ` (?l X1)" using 5
  hence "\<Union>(?ch ?e ` {?f p2}) \<subseteq> (\<Union>(?ch ?e `(?l X1)))" by force
(*
  hence "p2 \<in> ?ch ?e (?f p2)" using l2 by fast
  hence "p2 \<in> \<Union>(?ch ?e ` {?f p2})" by fastforce
  hence "p2 \<in> \<Union>(?ch ?e ` (?l X1))" using 3 tr
  hence "p2 \<in> partitionsconstructor ?e (?l X1)" using partitionsconstructor_def by metis
  hence "p2 \<in> (?l X2)" using 2 allpartitionsoflist_def by (metis allpartitionsoflist.simps(2))
*)
qed
}
show ?thesis sorry
oops

lemma fixes x fixes n shows "mypred x n" 
proof -
fix x
fix n
show "mypred x n"
proof (rule nat.induct)
  show "mypred x 0" using a7 mypred_def sorry
next
  fix m
  assume "mypred x m"
  show "mypred x (Suc m)" sorry
qed
qed

(*
theorem "all_partitions_classical (set X) = allpartitionsoflist (X::('a list))"
proof -
have 1: "all_partitions_classical (set []) = allpartitionsoflist ([]::('a list))" sorry
have 2: "\<forall> (x::'a) (Y::('a list)) . 
(all_partitions_classical (set Y) = allpartitionsoflist Y) \<longrightarrow>
(all_partitions_classical (set (x#Y)) = allpartitionsoflist (x#Y))
" sorry
have "\<forall> Y::('a list) . (all_partitions_classical (set Y) = allpartitionsoflist Y)"
using 1 2 sorry
qed

lemma fixes X x y assumes "is_partition (X \<union> {x})" and "y \<notin> \<Union> (X \<union> {x})" 
shows "is_partition (X-{x} \<union> {x \<union> {y}})"
proof -
have 1: "is_partition X" using a8 by (metis (full_types) assms(1) sup_ge1)
hence 2: "\<forall> x1 \<in> X . x1 \<noteq> {}" using is_partition_def by blast
have 3: "X \<subseteq> X \<union> {x \<union> {y}}" by fast
{fix x1
assume "x1 \<in> X \<union> {x \<union> {y}}" 
hence "x1 \<in> X \<or> x1 \<in> {x \<union> {y}}" by fast
hence "x1 \<noteq> {}" using 2 by blast
{
fix x2
assume "x2 \<in> X \<union> {x \<union> {y}} - {x1}"

} 
}
qed
*)
