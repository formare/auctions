(*
$Id$

Auction Theory Toolbox

Authors:
* Christoph Lange <math.semantic.web@gmail.com>
* Marco B. Caminati <marco.caminati@gmail.com>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

theory Partitions
imports Main Complete_Lattices
begin

(* don't need the following for now; just thought we might need it for computability:
(* True iff E is the set of all equivalence relations on the set X *)
definition isEquivSet :: "('a \<times> 'a) set set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "isEquivSet E X \<longleftrightarrow> (\<forall> e . e \<in> E \<longleftrightarrow> equiv X e)"
*)

text {* This inference rule is needed below; it combines Set.equalityI and Set.subsetI to a single step. *}
lemma equalitySubsetI: "(\<And>x . x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x . x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B" by fast

(*
Enumerating all partitions of a set by example:

Set: {a}
Partitions: {{a}}

Set: {a,b}
Partitions: {{a}, {b}}, {{a, b}}

Set: {a,b,c}
Partitions: {{a}, {b}, {c}}, {{a,b}, {c}}, {{a,c}, {b}}, {{a}, {c,b}}, {{a,b,c}}

http://en.wikipedia.org/wiki/Bell_number (number of partitions of a set = number of equivalence relations on a set)
*)

(* The following definition of "all partitions of a set" (defined as the set of all 
   quotients of the set by all equivalence relations on the set)
   is well-defined but not computable: *)
definition all_partitions_wrt_equiv :: "'a set \<Rightarrow> 'a set set set"
  where "all_partitions_wrt_equiv A = { P . (* all sets P such that \<dots> *)
    (* thought we'd need something like this for computability:
    P \<in> Pow (Pow A) (* P is a set of subsets of A,
                       i.e. a subset of the set of all subsets of A,
                       i.e. a subset of the powerset of A,
                       i.e. a member of the powerset of the powerset of A.
                       We need this only for computability; otherwise 'P = A // e' would do the job. *)
    \<and> *)
    (\<exists> R . (* There is an R such that \<dots> *)
      equiv A R (* R is an equivalence relation on A *)
      \<and> P = A // R (* and P is the partition of A w.r.t. R. *)
    ) }"

(* algorithmic function that computes all partitions of a set, based on lists *)
fun all_partitions_fun_list :: "'a list \<Rightarrow> 'a set list list"
  where "all_partitions_fun_list [] = []"
      | "all_partitions_fun_list [x] = [[{x}]]" (* singleton case is special, not sufficiently covered by [] and x#xs *)
      | "all_partitions_fun_list (x # xs) = (let xs_partitions = all_partitions_fun_list xs in
        concat [
          (* inserting x into each equivalence class (one at a time) \<dots> *)
          [ P[i := {x} \<union> P ! i] . i \<leftarrow> map nat [0..(int (List.length P) - 1)] ]
        . P \<leftarrow> xs_partitions (* \<dots> of each partition of xs *) ]
        @ [ {x} # P . P \<leftarrow> xs_partitions] (* and adding the {x} singleton equivalence class to each partition of xs: *)
        )"

(* need to turn 'a set list list into 'a set set set *)
fun all_partitions_fun :: "'a\<Colon>linorder set \<Rightarrow> 'a set set set"
  where "all_partitions_fun A = set (map set (all_partitions_fun_list (sorted_list_of_set A)))"

(* definition of a partition (without saying of what set it is a partition) *)
definition is_partition where
"is_partition P = (\<forall> x\<in>P . \<forall> y\<in> P . (x \<inter> y \<noteq> {} \<longleftrightarrow> x=y))"
(* alternative, less concise formalisation:
"is_partition P = (\<forall> ec1 \<in> P . ec1 \<noteq> {} \<and> (\<forall> ec2 \<in> P - {ec1}. ec1 \<inter> ec2 = {}))"
*)

(* checks whether something is a partition of a given set *)
definition is_partition_of where "is_partition_of P A = (\<Union> P = A \<and> is_partition P)"

(* classical set theory definition of "all partitions of a set" *)
definition all_partitions_classical where 
"all_partitions_classical A = {P . is_partition_of P A}"

(* MC: Here is some new material.  Next step: integrate new partitions definitions into auctions 
   (i.e. nVCG_CaseChecker.thy) *)
(* MC: A further, proof-friendlier way of computing partitions is introduced: 
   everything's a set, except the very initial input, which is a list 
   (of elements) because I don't know how to do recursive definitions 
   on finite sets.
   CL@MC: There is a predicate Finite_Set.finite, which is defined inductively (search for 
   "inductive finite" in Finite_Set.thy, but it is not defined as an algebraic _datatype_ and 
   therefore doesn't work with recursive _functions_.
   Then equivalence with all_partitions_classical is inductively shown *)
(* MC: update: now I probably would know how to utterly eliminate lists from this.
   CL@MC: Is this comment still up to date? *)

text {* inserts an element into a specified set inside the given set of sets *}
definition insert_into_member
(* CL@MC: you had originally referred to the given set of sets as a partition, and then stated:
   if the element (i.e. new_el) is fresh, we obtain again a partition.  The argument that I 
   have now renamed into "Sets" is not necessarily a partition, so you probably meant:
   If "Sets" is a partition of a set "Set",
   and S \<in> Sets is an equivalence class,
   and new_el \<notin> Set,
   then "insert_into_member new_el Sets S" is a partition of "Set \<union> {new_el}".
   Would it make sense to state this as a lemma and prove it? *)
:: "'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set"
where "insert_into_member new_el Sets S = Sets - {S} \<union> {S \<union> {new_el}}"

lemma insert_into_member_partition1:
  fixes elem::'a
    and P::"'a set set"
    and eq_class::"'a set"
  (* no need to assume "eq_class \<in> P" *)
  shows "\<Union> insert_into_member elem P eq_class = \<Union> (P - {eq_class}) \<union> (eq_class \<union> {elem})"
    unfolding insert_into_member_def
    by (metis Sup_insert Un_commute insert_is_Un)

(* TODO CL: as with insert_into_member above, what does the following function do when the given set of sets
   is not a partition?  And should we prove that, when the given set is a partition, this function 
   does what it is supposed to do? *)
text {* Assuming that @{text P} is a partition of a set @{text S}, and @{text "new_el \<notin> S"}, this function yields
  all possible partitions of @{text "S \<union> {new_el}"} that are coarser than @{text P}
  (i.e. not splitting equivalence classes that already exist in @{text P}).  These comprise one partition 
  with an equivalence class @{text "{new_el}"} and all other equivalence classes unchanged,
  as well as all partitions obtained by inserting @{text new_el} into one equivalence class of @{text P} at a time. *}
definition coarser_partitions_with ::"'a \<Rightarrow> 'a set set \<Rightarrow> 'a set set set"
where "coarser_partitions_with new_el P = 
  insert
  (* Let 'part' be a partition of a set 'Set',
     and suppose new_el \<notin> Set, i.e. {new_el} \<notin> part,
     then the following constructs a partition of 'Set \<union> {new_el}' obtained by
     inserting a new equivalence class {new_el} and leaving all previous equivalence classes unchanged. *)
  (insert {new_el} P)
  (* Let 'part' be a partition of a set 'Set',
     and suppose new_el \<notin> Set,
     then the following constructs
     the set of those partitions of 'Set \<union> {new_el}' obtained by
     inserting new_el into one equivalence class of 'part' at a time. *)
  ((insert_into_member new_el P) ` P)"

text {* Let @{text P} be a partition of a set @{text S}, and @{text elem} an element (which may or may not be
  in @{text S} already).  Then, any member of @{text "coarser_partitions_with elem P"} is a set of sets
  whose union is @{text "S \<union> {elem}"}, i.e.\ it satisfies a necessary criterion for being a partition of @{text "S \<union> {elem}"}.
*}
lemma coarser_partitions_covers:
  fixes elem::'a
    and P::"'a set set"
    and Q::"'a set set"
  assumes "Q \<in> coarser_partitions_with elem P"
  shows "\<Union> Q = insert elem (\<Union> P)"
proof -
  let ?S = "\<Union> P"
  have Q_cases: "Q \<in> (insert_into_member elem P) ` P \<or> Q = insert {elem} P"
    using coarser_partitions_with_def assms by (smt insertE)
  {
    fix eq_class assume eq_class_in_P: "eq_class \<in> P"
    have "\<Union> (P - {eq_class}) \<union> (eq_class \<union> {elem}) = ?S \<union> (eq_class \<union> {elem})"
      using insert_into_member_partition1
      by blast
    with eq_class_in_P have "\<Union> (P - {eq_class}) \<union> (eq_class \<union> {elem}) = ?S \<union> {elem}" by blast
    then have "\<Union> insert_into_member elem P eq_class = ?S \<union> {elem}"
      using insert_into_member_partition1
      by (rule subst)
  }
  then show ?thesis using Q_cases by blast
qed

text {* @{text "partition_without e"} reverses @{text "coarser_partitions_with e"}.
@{text coarser_partitions_with} is one-to-many, while this is one-to-one, so we can think of a tree relation,
where coarser partitions of a set @{text "S \<union> {elem}"} are child nodes of one partition of @{text S}. *}
definition partition_without :: "'a \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
where "partition_without elem P = { x - {elem} | x . x \<in> P } - {{}}"

(* TODO give it some name with "image", "Collect", "mem" *)
lemma image_Collect_mem: "{ f x | x . x \<in> S } = f ` S" by auto

lemma partition_without_covers:
  fixes elem::'a
    and P::"'a set set"
  shows "\<Union> partition_without elem P = \<Union> P - {elem}"
proof -
  have "\<Union> partition_without elem P = \<Union> (((\<lambda>x . x - {elem}) ` P) - {{}})"
    unfolding partition_without_def
    using image_Collect_mem by metis
  also have "\<dots> = \<Union> P - {elem}" by blast
  finally show ?thesis .
qed

lemma partition_without_is_partition:
  fixes elem::'a
    and P::"'a set set"
  assumes "is_partition P"
  shows "is_partition (partition_without elem P)"
proof - 
  let ?Q = "partition_without elem P"
  show ?thesis
  proof -   
    have "\<forall> x1 \<in> ?Q. \<forall> x2 \<in> ?Q. x1 \<inter> x2 \<noteq> {} \<longleftrightarrow> x1 = x2"
    proof 
      fix x1 assume x1_in_Q: "x1 \<in> ?Q"
      then obtain z1 where z1_in_P: "z1 \<in> P" and z1_sup: "x1 = z1 - {elem}"
        unfolding partition_without_def
        by (smt mem_Collect_eq set_diff_eq)
      have x1_non_empty: "x1 \<noteq> {}" using x1_in_Q partition_without_def by fast
      show "\<forall> x2 \<in> ?Q. x1 \<inter> x2 \<noteq> {} \<longleftrightarrow> x1 = x2" 
      proof
        fix x2 assume "x2 \<in> ?Q"
        then obtain z2 where z2_in_P: "z2 \<in> P" and z2_sup: "x2 = z2 - {elem}"
          unfolding partition_without_def
          by (smt mem_Collect_eq set_diff_eq)
        have "x1 \<inter> x2 \<noteq> {} \<longrightarrow> x1 = x2"
        proof
          assume "x1 \<inter> x2 \<noteq> {}"
          then have "z1 \<inter> z2 \<noteq> {}" using z1_sup z2_sup by fast
          then have "z1 = z2" using z1_in_P z2_in_P assms by (metis is_partition_def)
          then show "x1 = x2" using z1_sup z2_sup by fast
        qed
        moreover have "x1 = x2 \<longrightarrow> x1 \<inter> x2 \<noteq> {}" using x1_non_empty by auto
        ultimately show "(x1 \<inter> x2 \<noteq> {}) \<longleftrightarrow> x1 = x2" by blast
      qed
    qed
    then show ?thesis using is_partition_def by auto
  qed
qed

definition all_coarser_partitions_with :: " 'a \<Rightarrow> 'a set set set \<Rightarrow> 'a set set set"
where "all_coarser_partitions_with elem P = \<Union> coarser_partitions_with elem ` P"

fun all_partitions_of_list :: "'a list \<Rightarrow> 'a set set set"
where 
"all_partitions_of_list [] = {{}}" |
"all_partitions_of_list (e # X) = all_coarser_partitions_with e (all_partitions_of_list X)" 

text {* A subset of a partition is also a partition (but, note: only of a subset of the original set) *}
lemma subset_is_partition:
  assumes subset: "P \<subseteq> Q"
      and partition: "is_partition Q"
  shows "is_partition P"
proof -
  {
    fix x y assume "x \<in> P \<and> y \<in> P"
    then have "x \<in> Q \<and> y \<in> Q" using subset by fast
    then have "x \<inter> y \<noteq> {} \<longleftrightarrow> x = y" using partition is_partition_def by metis
  }
  then show ?thesis using is_partition_def by blast
qed

lemma partition_extension:
  fixes P::"'a set set"
    and X::"'a set"
  assumes partition: "is_partition P"
      and disjoint: "X \<inter> \<Union> P = {}" 
      and non_empty: "X \<noteq> {}"
  shows "is_partition (insert X P)"
proof -
  {
    fix x y assume x_y_in_ext: "x \<in> insert X P \<and> y \<in> insert X P"
    have "x \<inter> y \<noteq> {} \<longleftrightarrow> x = y"
    proof
      assume "x \<inter> y \<noteq> {}"
      then show "x = y"
        using x_y_in_ext partition disjoint
        unfolding is_partition_def
        by fast
    next
      assume "x = y"
      then show "x \<inter> y \<noteq> {}"
        using x_y_in_ext partition non_empty
        unfolding is_partition_def
        by auto
    qed
  }
  then show ?thesis unfolding is_partition_def by force
qed

lemma disj_eq_classes:
  fixes P::"'a set set"
    and X::"'a set"
  assumes "is_partition P"
      and "X \<in> P"
  shows "X \<inter> \<Union> (P - {X}) = {}" 
proof -
  {
    fix x
    assume x_in_two_eq_classes: "x \<in> X \<inter> \<Union> (P - {X})"
    then obtain Y where other_eq_class: "Y \<in> P - {X} \<and> x \<in> Y" by blast
    have "x \<in> X \<inter> Y \<and> Y \<in> P"
      using x_in_two_eq_classes other_eq_class by force
    then have "X = Y" using assms is_partition_def by fast
    then have "x \<in> {}" using other_eq_class by fast
  }
  then show ?thesis by blast
qed

lemma l4: fixes newel part Subset assumes "newel \<notin> \<Union> part" and "Subset \<in> part"
and "is_partition part"
shows "is_partition (insert_into_member newel part Subset)" 
proof -
  let ?g="insert_into_member newel" let ?q="part"  let ?X="Subset"
  let ?p="?q - {?X}" let ?Y="insert newel ?X" let ?P="is_partition"
  have 1: "is_partition ?p" using subset_is_partition assms by blast
  have "?X \<inter> \<Union> ?p = {}" using assms l7 by metis
  hence "?Y \<noteq> {} \<and> ?Y \<inter> \<Union> ?p={}" using assms by blast
  hence "?P (insert ?Y ?p)" using partition_extension assms 1 by metis
  hence "?P (?p \<union> {?X \<union> {newel}})" by fastforce
  thus "?P (?g ?q ?X)" using insert_into_member_def by metis
qed

lemma l1: fixes e p assumes "is_partition p1" and 
"p2 \<in> (coarser_partitions_with e p1)" and "e \<notin> \<Union> p1"
shows "is_partition p2"
proof -
  let ?g = "insert_into_member e" let ?q="insert {e} p1" let ?P="is_partition"
  have 1: "p2 \<in> insert (insert {e} p1) ((?g p1)`p1)" 
  using assms coarser_partitions_with_def by metis
  have 2: "?P ?q" using partition_extension assms by fastforce
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
shows "q \<in> coarser_partitions_with e (partition_without e q)"
proof -
  let ?c="coarser_partitions_with e" let ?p="partition_without e q" let ?g="insert_into_member e"
  let ?f="%x . x - {e}" let ?P="is_partition"
  obtain y where 1: "y \<in> q \<and> e \<in> y" using assms by (metis UnionE)
  let ?q2="q-{y}" let ?x="y-{e}"
  have 8: "?P ?q2" using subset_is_partition assms by blast
  have 5: "?x = ?f y \<and> ?f`{y}={?x} " by fast hence 
  4: "?x \<in> ?f ` q " using 1 by blast
  have "\<forall> w \<in> ?q2 . w \<inter> y = {}" using is_partition_def assms 1 4 
  by (metis Diff_iff insertI1)
  hence "\<forall> w \<in> ?q2 . e \<notin> w" using is_partition_def assms 1 4 by blast
  hence "\<forall> w \<in> ?q2 . ?f w = id w" by simp
  hence "?f ` ?q2 = id ` ?q2" by blast
  hence "?f ` ?q2 = ?q2 \<and> q=?q2 \<union> {y}" using 1 by force
  hence 7: "?p=?q2 \<union> {?x} - {{}}" using 1 partition_without_def l10 5 sorry (* TODO CL: sorry, can't prove this right now after refactorings, will fix later *)
  {
    assume "?x \<notin> ?p" hence "?x \<in> {{}}" using 4 partition_without_def sorry (* TODO CL: sorry, can't prove this right now after refactorings, will fix later *)
    hence 9: "?x={} \<and> y={e}" using 1 by fast
    hence "?p = ?q2 - {{}}" using 7 is_partition_def assms by force
    hence 10: "?p = ?q2" using l11 8 by blast
    have "insert {e} ?q2 = insert y ?q2" using 9 by fast
    hence "insert {e} ?q2 = q" using 1 by auto
    hence "insert {e} ?p = q" using 10 by presburger
    hence "q \<in> ?c ?p" using coarser_partitions_with_def by (metis insertI1)    
  } 
  hence 11: "?x \<notin> ?p \<longrightarrow> ?thesis" by fast
  have "?x={} \<or> ?x \<notin> q" using partition_extension 1 assms is_partition_def 
  by (smt Diff_Int_distrib2 Diff_iff Int_absorb empty_Diff insert_iff)
  hence "?x \<notin> q" using is_partition_def by (metis Int_empty_left assms(1))
  hence 0: "?q2 - {?x} = ?q2" by fastforce
{
  assume 2: "?x \<in> ?p" 
  hence "?x \<noteq> {}" using l11 partition_without_is_partition assms by metis
  hence 12: "?q2 \<union> {?x} - {{}} = ?q2 \<union> {?x}" using l11 8 assms by blast
  have "?g ({?x} \<union> ?q2) (?x) = ({?x} \<union> ?q2) - {?x} \<union> {?x \<union> {e}} " 
  using insert_into_member_def assms 0 by metis
  hence "?g ({?x} \<union> ?q2) ?x = ({} \<union> ?q2) \<union> {?x \<union> {e}}" 
  using 0 by force
  hence "?g ({?x} \<union> ?q2) ?x = ?q2 \<union> {y}" using 1 by blast
  hence "?q2 \<union> {y} = ?g ?p ?x" using 7 12 partition_without_def by force
  hence "{y} \<union> ?q2 \<in> ?g ?p ` ?p" using 2 image_def by blast
  hence "{y} \<union> ?q2 \<in> ?c ?p" using coarser_partitions_with_def by (metis insertCI)
}
  thus ?thesis using 11 by (metis `y \<in> q \<and> e \<in> y` insert_Diff_single insert_absorb insert_is_Un)
qed

(* MC: norepetitions stuff could be moved to a 
separate thy of more general material*)
definition norepetitions where "norepetitions l \<longleftrightarrow> card (set l) = length l"

lemma fixes l shows "norepetitions l \<longleftrightarrow> (card (set l) \<ge> length l)" 
using norepetitions_def by (metis card_length le_antisym)

lemma noreptl: fixes l assumes "norepetitions l" shows "norepetitions (tl l)" 
using assms norepetitions_def by (metis card_distinct distinct_card distinct_tl) 

definition mypred ::" 'a => nat => bool" where "mypred x n = 
(\<forall> X::('a list) . (length X=n \<and> norepetitions X \<longrightarrow> 
all_partitions_classical (set X) = all_partitions_of_list X))"

lemma indstep: fixes x::"'a" fixes n::nat assumes "mypred x n" shows "mypred x (Suc n)"   
proof -
  let ?l = "all_partitions_of_list" let ?c = "all_partitions_classical" 
  let ?ch = "coarser_partitions_with" let ?P="is_partition" let ?Q="is_partition_of"
  have indhyp: "\<forall> X::('a list) . length X = n \<and> norepetitions X \<longrightarrow> (?c (set X) = ?l X)" 
  using mypred_def assms by fast
  (* what's the difference with def l == "allpartitionsoflist" (which doesn't work)?? *)
  have "\<forall> X::('a list) . ((length X=Suc n \<and> norepetitions X) \<longrightarrow> 
  (all_partitions_classical (set X) = all_partitions_of_list X))" 
  proof 
  fix X2::"'a list"
  let ?e = "hd X2" let ?f = "partition_without ?e" let ?n2 = "length X2" 
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
      have 16: "\<Union> (?f p2) = \<Union> p2 - {?e}" using partition_without_covers by metis
      assume "p2 \<in> ?c (set X2)"
      hence "?Q p2 (set X2)" using all_partitions_classical_def by fast
      hence 14: "?P p2 \<and> ?e \<in> (set X2) \<and> \<Union> p2=(set X2)" 
      using is_partition_of_def 2 by (metis hd_in_set list.distinct(1))
      have 18: "\<Union> (?f p2)= set ?X1" using 2 16 partition_without_covers 19 14 by (metis Diff_insert_absorb List.set.simps(2))
      have "?P (?f p2)" using partition_without_is_partition 14 by fast
      hence "?Q (?f p2) (set ?X1)" using is_partition_of_def 18 by blast
      hence "(?f p2) \<in> ?c (set ?X1)" using all_partitions_classical_def by blast
      hence 5: "?f p2 \<in> ?l ?X1" using indhyp mypred_def 13 a12 by blast
      hence "p2 \<in> (?ch ?e) (?f p2)" using l2a 14 by fast
      hence "p2 \<in> \<Union> ((?ch ?e) ` (?l ?X1))" using 5 by blast
      thus "p2 \<in> (?l X2)" using all_coarser_partitions_with_def 2 
      by (metis all_partitions_of_list.simps(2)) 
    qed
    have a2: "?l X2 \<subseteq> ?c (set X2)"
    proof -
      {
      fix p2  assume "p2 \<in> ?l X2"
      hence "p2 \<in> all_coarser_partitions_with ?e (?l ?X1)" using 2 
      by (metis all_partitions_of_list.simps(2)) 
      hence a3: "p2 \<in> \<Union> (?ch ?e ` (?l ?X1))" using all_coarser_partitions_with_def by metis
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
      have "\<Union> p2 = (set ?X1) \<union> {?e}" using a11 a5 a7 coarser_partitions_covers by fast
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

lemma emptyparts1: shows "is_partition_of {} {}" 
using assms is_partition_def is_partition_of_def by (metis Union_empty empty_iff)

lemma emptyparts2: fixes x assumes "is_partition_of x {}" shows "x={}" 
using assms is_partition_def is_partition_of_def by fast

lemma emptyparts: shows "all_partitions_classical {} = {{}}" 
using emptyparts1 emptyparts2 all_partitions_classical_def by blast

lemma l14: fixes x fixes n shows "mypred x n" 
proof -
fix x fix n
show "mypred x n"
proof (rule nat.induct)
  show "mypred x 0" using mypred_def emptyparts 
by (metis all_partitions_of_list.simps(1) length_0_conv set_empty2)
next
  fix m assume "mypred x m" thus "mypred x (Suc m)" using indstep by metis
qed
qed

theorem partadequacy: fixes l assumes "norepetitions l" shows 
"all_partitions_of_list l = all_partitions_classical (set l)" 
using l14 mypred_def assms by fast

lemma cardsize: fixes x assumes "finite x"
shows "length (sorted_list_of_set x) = card x" using assms by 
(metis finite_list length_remdups_card_conv length_sort sorted_list_of_set_sort_remdups)

lemma setlistid: fixes x assumes "finite x"
shows "set (sorted_list_of_set x)=x" using assms by simp

lemma norepset: fixes x assumes "finite x" shows 
"norepetitions (sorted_list_of_set x)" 
using assms cardsize setlistid norepetitions_def by metis

definition all_partitions where "all_partitions X = all_partitions_of_list (sorted_list_of_set X)"

corollary fixes X assumes "finite X" shows 
"all_partitions X = all_partitions_classical X" 
unfolding all_partitions_def
using norepset partadequacy assms by fastforce
(* all_partitions internally works with a list representing a set
   (this allows us to use the recursive function all_partitions_of_list).
   For a list with repetitions we can only guarantee compliance
   once we establish norepetitions. *)

end
