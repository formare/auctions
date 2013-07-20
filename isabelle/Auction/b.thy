theory b
imports Main a c
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

(* CL@MC: please document the intuition behind this!  It would take me a lot of time to figure
   this out for myself by example. 
definition growpart
::"'a \<Rightarrow> ('a set \<times> ('a set set)) \<Rightarrow> 'a set set" 
where "growpart elem x=snd x - {fst x} \<union> {fst x \<union> {elem}}"

definition childrenofpartition 
::"'a => ('a set set) => ('a set set set)" 
where 
"childrenofpartition e p = insert (insert {e} p) ((growpart e) ` (p \<times> {p}))"
*)

definition growpart2
(* adds an element to a specified set of a specified partition. 
If this element is fresh, we obtain again a partition *)
:: "'a => 'a set set => 'a set => 'a set set"
where "growpart2 newel part Subset = part - {Subset} \<union> {Subset \<union> {newel}}"

definition childrenofpartition2 ::"'a => ('a set set) => ('a set set set)"
(* Yields all the possible partitions coarser than part and 
obtainable by adding a fixed new element newel *)
where "childrenofpartition2 newel part = 
insert (insert {newel} part) ((growpart2 newel part) ` part)"

lemma l12: fixes e p assumes "q\<in>(childrenofpartition2 e p)" shows 
  "\<Union> q = insert e (\<Union> p)"
proof -
  let ?ch="childrenofpartition2 e" let ?Q="\<Union> q" let ?g="growpart2 e" let ?P="\<Union> p"
  have 3: "q\<in>(?g p)`p \<or> q=insert {e} p"
  using childrenofpartition2_def assms by (smt insertE)
  have 4: "\<Union> (insert {e} p)= insert e (\<Union> p)" by auto
  {
    fix x assume 1: "x \<in> p"
    hence 2: "\<Union> ((?g p) x) = \<Union> (p - {x}) \<union> (x \<union> {e})" using growpart2_def 
    by (metis Sup_insert Un_commute insert_is_Un)
    have "\<Union> (p - {x}) \<union> (x \<union> {e}) = \<Union> p \<union> (x \<union> {e})" by blast
    hence "\<Union> (p - {x}) \<union> (x \<union> {e}) = \<Union> p \<union> {e}" using 1 by blast
    hence "\<Union> ((?g p) x) = \<Union> p \<union> {e}" using 2 by presburger
  }
  thus ?thesis using 3 4 by blast
qed

definition parent :: " 'a => 'a set set => 'a set set" 
(*parent e reverses childrenofpartition e.
children is one-to-many, while this is one-to-one (father is unique)*)
where "parent e p = ((%x . x - {e}) ` p) - {{}}"

lemma l13: fixes e q shows "\<Union> (parent e q)=\<Union> q - {e}"
proof -
  let ?E="{e}" let ?f="%x . (x - ?E)" let ?p="parent e q" 
  have "\<forall> x \<in> ?f ` q . x \<subseteq> \<Union> q - ?E" using image_def by fast
  hence "\<Union> (?f ` q) = \<Union> q - ?E" by blast
  thus ?thesis using parent_def by (metis Sup_insert Un_empty_left insert_Diff_single)
qed

lemma l3: fixes e q assumes "is_partition q" shows "is_partition (parent e q)"
proof - 
  let ?p = "parent e q"  let ?f="%x . (x - {e})" 
  show "is_partition (parent e q)"
  proof -   
    have 10: "\<forall> x1 \<in> ?p. \<forall> x2 \<in> ?p. (x1 \<inter> x2 \<noteq> {} \<longleftrightarrow> x1=x2)"
    proof 
      fix x1 assume 7: "x1 \<in> ?p"
      hence "x1 \<in> ?f ` q" using parent_def by (metis (full_types) Diff_iff)
      then obtain z1 where 1: "z1 \<in> q \<and> x1 = ?f z1" using image_def by blast 
      have 3: "z1 \<in> q \<and> x1 = z1 - {e}" using 1 by fast
      have 6: "x1 \<noteq> {}" using 7 parent_def by fast
      show "\<forall> x2 \<in> ?p. (x1 \<inter> x2 \<noteq> {}) \<longleftrightarrow> x1=x2" 
      proof
        fix x2 assume "x2 \<in> ?p"
        hence "x2 \<in> ?f ` q" using parent_def by (metis (full_types) Diff_iff)
        then obtain z2 where 2: "z2 \<in> q \<and> x2 = ?f z2" using image_def by blast
        have 4: "z2 \<in> q \<and> x2 = z2 - {e}" using 2 by fast
        hence 7: "x2 \<subseteq> z2" by fast
        have 11: "x1 \<inter> x2 \<noteq> {} \<longrightarrow> x1=x2" 
        proof
          assume "x1 \<inter> x2 \<noteq> {}" hence "z1 \<inter> z2 \<noteq> {}" using 3 4 by fast
          hence "z1 = z2" using assms 3 4 is_partition_def by metis
          thus "x1=x2" using 3 4 by fast
        qed
        have "x1=x2 \<longrightarrow> x1 \<inter> x2 \<noteq> {}"
        proof 
          assume "x1=x2" 
          thus "x1 \<inter> x2 \<noteq>{}" using 6 by (metis inf_idem)
        qed
      thus "(x1 \<inter> x2 \<noteq> {}) \<longleftrightarrow> x1=x2" using 11 by linarith     
      qed
    qed (*10*)
    thus ?thesis using is_partition_def by auto
  qed
qed

definition partitionsconstructor 
:: " 'a => 'a set set set => 'a set set set"
where "partitionsconstructor e P = \<Union> (childrenofpartition2 e ` P)"

fun allpartitionsoflist (* input is a list representing a set (see comment above), 
hence output from a list with repetitions is not guaranteed compliance *)
::"'a list => 'a set set set"
where 
"allpartitionsoflist []={{}}"|
"allpartitionsoflist (e # X) = partitionsconstructor e (allpartitionsoflist X)" 

definition allpartitions where "allpartitions X = allpartitionsoflist (sorted_list_of_set X)"

lemma l5: fixes p q assumes "is_partition q" assumes "p \<subseteq> q" shows "is_partition p"
proof -
  let ?Q = "is_partition" let ?P="%x . %y . (x \<inter> y \<noteq> {} \<longleftrightarrow> x=y)"
  {
    fix x y assume "x\<in>p \<and> y\<in>p"     
    hence "x\<in>q \<and> y\<in>q" using assms by fast    
    hence "?P x y" using assms is_partition_def by metis
  }
  thus "?Q p" using is_partition_def by blast
qed

lemma l6: fixes p X assumes "is_partition p" assumes "X \<inter> \<Union> p = {}" 
assumes "X \<noteq> {} " shows "is_partition (insert X p)"
proof -
  let ?P="is_partition" let ?Y="insert X p" let ?p="%a . %b . (a \<inter> b \<noteq> {} \<longleftrightarrow> a=b)"
  {
    fix x y assume 1: "x\<in>?Y \<and> y\<in>?Y"
    have 2: "(x=X \<and> y\<in>p) \<longrightarrow> ?p x y" using assms is_partition_def by blast
    hence 4: "((x=X \<and> y\<in>p) \<or> (y=X \<and> x\<in>p)) \<longrightarrow> ?p x y" using assms by blast
    have 3: "x=X \<and> y=X \<longrightarrow> ?p x y" using assms by fastforce
    hence 5: "x=X \<or> y=X \<longrightarrow> ?p x y" using assms 1 4 by fast
    have "(\<not> (x=X \<or> y=X)) \<longrightarrow> ?p x y" using assms is_partition_def 1 by (metis insertE)
    hence "?p x y" using 5 by fastforce
  }
  thus "?P ?Y" using is_partition_def by metis
qed

lemma l7: fixes q X assumes "is_partition q" assumes "X\<in>q" shows
"X \<inter> \<Union> (q - {X})={}" 
proof -
  let ?p="q-{X}" 
  {
    fix x assume 
    0:"x\<in> X \<inter> \<Union> ?p" then obtain Y where 
    1: "Y\<in>?p \<and> x\<in>Y" by blast
    have "x \<in> X \<inter> Y \<and> Y\<in>q" using 0 1 by force
    hence "X=Y" using assms is_partition_def by fast
    hence "False" using 1 by fast
  }
  thus ?thesis by blast
qed

lemma l4: fixes newel part Subset assumes "newel \<notin> \<Union> part" and "Subset \<in> part"
and "is_partition part"
shows "is_partition (growpart2 newel part Subset)" 
proof -
  let ?g="growpart2 newel" let ?q="part"  let ?X="Subset"
  let ?p="?q - {?X}" let ?Y="insert newel ?X" let ?P="is_partition"
  have 1: "is_partition ?p" using l5 assms by blast
  have "?X \<inter> \<Union> ?p = {}" using assms l7 by metis
  hence "?Y \<noteq> {} \<and> ?Y \<inter> \<Union> ?p={}" using assms by blast
  hence "?P (insert ?Y ?p)" using l6 assms 1 by metis
  hence "?P (?p \<union> {?X \<union> {newel}})" by fastforce
  thus "?P (?g ?q ?X)" using growpart2_def by metis
qed

lemma l1: fixes e p assumes "is_partition p1" and 
"p2 \<in> (childrenofpartition2 e p1)" and "e \<notin> \<Union> p1"
shows "is_partition p2"
proof -
  let ?g = "growpart2 e" let ?q="insert {e} p1" let ?P="is_partition"
  have 1: "p2 \<in> insert (insert {e} p1) ((?g p1)`p1)" 
  using assms childrenofpartition2_def by metis
  have 2: "?P ?q" using l6 assms by fastforce
  {
  assume "\<not> ?thesis"
  hence "p2 \<noteq> ?q" using 2 by fast
  hence "p2 \<in> (?g p1)`p1" using 1 assms by fastforce
  then obtain X where 2: "X \<in> p1 \<and> p2 = (?g p1) X" by fast
  hence "?P p2" using l4 2 assms by fast
  }
  thus ?thesis by fast
qed

lemma l10: fixes f X Y shows "f`(X \<union> Y) = f`X \<union> (f`Y)" 
using Set.image_def by blast

lemma l11: fixes p assumes "is_partition p" shows "{} \<notin> p" 
using assms is_partition_def by fast

lemma l2a: fixes e q assumes "is_partition q" assumes "e \<in> \<Union> q" 
shows "q \<in> childrenofpartition2 e (parent e q)"
proof -
  let ?c="childrenofpartition2 e" let ?p="parent e q" let ?g="growpart2 e"
  let ?f="%x . x - {e}" let ?P="is_partition"
  obtain y where 1: "y \<in> q \<and> e \<in> y" using assms by (metis UnionE)
  let ?q2="q-{y}" let ?x="y-{e}"
  have 8: "?P ?q2" using l5 assms by blast
  have 5: "?x = ?f y \<and> ?f`{y}={?x} " by fast hence 
  4: "?x \<in> ?f ` q " using 1 by blast
  have "\<forall> w \<in> ?q2 . w \<inter> y = {}" using is_partition_def assms 1 4 
  by (metis Diff_iff insertI1)
  hence "\<forall> w \<in> ?q2 . e \<notin> w" using is_partition_def assms 1 4 by blast
  hence "\<forall> w \<in> ?q2 . ?f w = id w" by simp
  hence "?f ` ?q2 = id ` ?q2" by blast
  hence "?f ` ?q2 = ?q2 \<and> q=?q2 \<union> {y}" using 1 by force
  hence 7: "?p=?q2 \<union> {?x} - {{}}" using 1 parent_def l10 5 by metis
  {
    assume "?x \<notin> ?p" hence "?x \<in> {{}}" using 4 parent_def by force
    hence 9: "?x={} \<and> y={e}" using 1 by fast
    hence "?p = ?q2 - {{}}" using 7 is_partition_def assms by force
    hence 10: "?p = ?q2" using l11 8 by blast
    have "insert {e} ?q2 = insert y ?q2" using 9 by fast
    hence "insert {e} ?q2 = q" using 1 by auto
    hence "insert {e} ?p = q" using 10 by presburger
    hence "q \<in> ?c ?p" using childrenofpartition2_def by (metis insertI1)    
  } 
  hence 11: "?x \<notin> ?p \<longrightarrow> ?thesis" by fast
  have "?x={} \<or> ?x \<notin> q" using l6 1 assms is_partition_def 
  by (smt Diff_Int_distrib2 Diff_iff Int_absorb empty_Diff insert_iff)
  hence "?x \<notin> q" using is_partition_def by (metis Int_empty_left assms(1))
  hence 0: "?q2 - {?x} = ?q2" by fastforce
{
  assume 2: "?x \<in> ?p" 
  hence "?x \<noteq> {}" using l11 l3 assms by metis
  hence 12: "?q2 \<union> {?x} - {{}} = ?q2 \<union> {?x}" using l11 8 assms by blast
  have "?g ({?x} \<union> ?q2) (?x) = ({?x} \<union> ?q2) - {?x} \<union> {?x \<union> {e}} " 
  using growpart2_def assms 0 by metis
  hence "?g ({?x} \<union> ?q2) ?x = ({} \<union> ?q2) \<union> {?x \<union> {e}}" 
  using 0 by force
  hence "?g ({?x} \<union> ?q2) ?x = ?q2 \<union> {y}" using 1 by blast
  hence "?q2 \<union> {y} = ?g ?p ?x" using 7 12 parent_def by force
  hence "{y} \<union> ?q2 \<in> ?g ?p ` ?p" using 2 image_def by blast
  hence "{y} \<union> ?q2 \<in> ?c ?p" using childrenofpartition2_def by (metis insertCI)
}
  thus ?thesis using 11 by (metis `y \<in> q \<and> e \<in> y` insert_Diff_single insert_absorb insert_is_Un)
qed

definition mypred ::" 'a => nat => bool" where "mypred x n = 
(\<forall> X::('a list) . (length X=n \<and> norepetitions X \<longrightarrow> 
all_partitions_classical (set X) = allpartitionsoflist X))"

lemma fixes x shows "mypred x 0" 
using mypred_def emptyparts by (metis allpartitionsoflist.simps(1) length_0_conv set_empty2)

lemma indstep: fixes x::"'a" fixes n::nat assumes "mypred x n" shows "mypred x (Suc n)"   
proof -
  let ?l = "allpartitionsoflist" let ?c = "all_partitions_classical" 
  let ?ch = "childrenofpartition2" let ?P="is_partition" let ?Q="is_partition_of"
  have indhyp: "\<forall> X::('a list) . length X = n \<and> norepetitions X \<longrightarrow> (?c (set X) = ?l X)" 
  using mypred_def assms by fast
  (* what's the difference with def l == "allpartitionsoflist" (which doesn't work)?? *)
  have "\<forall> X::('a list) . ((length X=Suc n \<and> norepetitions X) \<longrightarrow> 
  (all_partitions_classical (set X) = allpartitionsoflist X))" 
  proof 
  fix X2::"'a list"
  let ?e = "hd X2" let ?f = "parent ?e" let ?n2 = "length X2" 
  let ?X1="tl X2" (* could use drop or sublist instead of tl *)
  show "(?n2=Suc n \<and> norepetitions X2) \<longrightarrow> (?c (set X2) = ?l X2)"
  proof
    assume a10: "?n2 = Suc n \<and> norepetitions X2"
    hence "X2=[?e]@?X1" 
    by (metis append_Cons append_Nil hd.simps length_Suc_conv tl.simps(2))
    hence 2: "X2=?e # ?X1" by fastforce
    have 13: "length ?X1=n" using a10 2 assms  
    by (metis diff_Suc_1 length_tl)
    have a12: "norepetitions ?X1" using a10 noreptl by fast
    hence "\<not> {?e} \<subseteq> set ?X1" using norepetitions_def tl_def set_def hd_def by 
    (smt "2" List.set.simps(2) a10 card_length impossible_Cons insert_absorb insert_subset)
    hence 19: "?e \<notin> set ?X1" by fast
    have a1: "?c (set X2) \<subseteq> ?l X2"
    proof
      fix p2
      have 16: "\<Union> (?f p2) = \<Union> p2 - {?e}" using l13 by metis
      assume "p2 \<in> ?c (set X2)"
      hence "?Q p2 (set X2)" using all_partitions_classical_def by fast
      hence 14: "?P p2 \<and> ?e \<in> (set X2) \<and> \<Union> p2=(set X2)" 
      using is_partition_of_def 2 by (metis hd_in_set list.distinct(1))
      have 18: "\<Union> (?f p2)= set ?X1" using 2 16 l13 19 14 by (metis Diff_insert_absorb List.set.simps(2))
      have "?P (?f p2)" using l3 14 by fast
      hence "?Q (?f p2) (set ?X1)" using is_partition_of_def 18 by blast
      hence "(?f p2) \<in> ?c (set ?X1)" using all_partitions_classical_def by blast
      hence 5: "?f p2 \<in> ?l ?X1" using indhyp mypred_def 13 a12 by blast
      hence "p2 \<in> (?ch ?e) (?f p2)" using l2a 14 by fast
      hence "p2 \<in> \<Union> ((?ch ?e) ` (?l ?X1))" using 5 by blast
      thus "p2 \<in> (?l X2)" using partitionsconstructor_def allpartitionsoflist_def 2 
      by (metis allpartitionsoflist.simps(2)) 
    qed
    have a2: "?l X2 \<subseteq> ?c (set X2)"
    proof -
      {
      fix p2  assume "p2 \<in> ?l X2"
      hence "p2 \<in> partitionsconstructor ?e (?l ?X1)" using 2 allpartitionsoflist_def 
      by (metis allpartitionsoflist.simps(2)) 
      hence a3: "p2 \<in> \<Union> (?ch ?e ` (?l ?X1))" using partitionsconstructor_def by metis
      obtain Y where a4: "Y \<in> (?ch ?e ` (?l ?X1))" and a5: "p2 \<in> Y" using a3 by blast
      obtain p1 where a6: "p1 \<in> (?l ?X1)" and a7: "Y = (?ch ?e p1)" using a4 by blast
      have a9: "p2 \<in> (?ch ?e p1)" using a5 a7 by fast
      have "length ?X1 = n" using 2 a10 by (metis One_nat_def Suc_eq_plus1 diff_Suc_1 list.size(4))
      hence "?c (set ?X1) = ?l ?X1" using indhyp mypred_def a12 by blast
      hence "p1 \<in> ?c (set ?X1)" using a6 indhyp mypred_def by blast
      hence "?Q p1 (set ?X1)" using all_partitions_classical_def by blast
      hence a11: "?P p1 \<and> \<Union> p1=set ?X1" 
      using is_partition_of_def by blast
      hence 22: "?P p2" using l1 a9 19 by fast
      have "\<Union> p2 = (set ?X1) \<union> {?e}" using a11 a5 a7 l12 by fast
      hence "\<Union> p2 = (set X2)" using 19 by (metis "2" List.set.simps(2) Un_commute insert_is_Un)
      hence "?Q p2 (set X2)" using 22 is_partition_of_def by blast
      hence "p2 \<in> ?c (set X2)" using all_partitions_classical_def by fastforce
      }
      thus ?thesis by fast
    qed
    show "?c (set X2) = ?l X2" using a1 a2 by fastforce
  qed
  qed
  thus ?thesis using mypred_def by fast
qed

lemma l14: fixes x fixes n shows "mypred x n" 
proof -
fix x fix n
show "mypred x n"
proof (rule nat.induct)
  show "mypred x 0" using mypred_def emptyparts 
by (metis allpartitionsoflist.simps(1) length_0_conv set_empty2)
next
  fix m assume "mypred x m" thus "mypred x (Suc m)" using indstep by metis
qed
qed

theorem partadequacy: fixes l assumes "norepetitions l" shows 
"allpartitionsoflist l = all_partitions_classical (set l)" 
using l14 mypred_def assms by fast

corollary fixes x assumes "finite x" shows 
"allpartitionsoflist (sorted_list_of_set x) = all_partitions_classical x" 
using norepset partadequacy assms by fastforce

definition allpartitionsofset where 
"allpartitionsofset x = allpartitionsoflist (sorted_list_of_set x)"

end

