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
imports Main SetUtils
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

lemma partition_extension1:
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

lemma partition_extension2:
  fixes new_el::'a
    and P::"'a set set"
    and X::"'a set"
  assumes partition: "is_partition P"
      and eq_class: "X \<in> P"
      and new: "new_el \<notin> \<Union> P"
shows "is_partition (insert_into_member new_el P X)"
proof -
  let ?Y = "insert new_el X"
  have rest_is_partition: "is_partition (P - {X})"
    using partition subset_is_partition by blast
  have "X \<inter> \<Union> (P - {X}) = {}"
   using eq_class partition disj_eq_classes
   by metis
  then have "?Y \<noteq> {} \<and> ?Y \<inter> \<Union> (P - {X}) = {}" using new by blast
  then have "is_partition (insert ?Y (P - {X}))"
    using rest_is_partition partition_extension1
    by metis
  then have "is_partition (P - {X} \<union> {X \<union> {new_el}})" by simp
  then show ?thesis using insert_into_member_def by metis
qed

lemma partition_extension3:
  fixes elem::'a
    and P::"'a set set"
    and Q::"'a set set"
  assumes P_partition: "is_partition P"
      and new_elem: "elem \<notin> \<Union> P"
      and Q_coarser: "Q \<in> coarser_partitions_with elem P"
  shows "is_partition Q"
proof -
  let ?q = "insert {elem} P"
  have Q_coarser_unfolded: "Q \<in> insert ?q (insert_into_member elem P ` P)" 
    using Q_coarser 
    unfolding coarser_partitions_with_def
    by fast
  show ?thesis
  proof (cases "Q = ?q")
    case True
    then show ?thesis
      using P_partition new_elem partition_extension1
      by fastforce
  next
    case False
    then have "Q \<in> (insert_into_member elem P) ` P" using Q_coarser_unfolded by fastforce
    then show ?thesis using partition_extension2 P_partition new_elem by fast
  qed
qed

lemma no_empty_eq_class:
  assumes "is_partition p"
  shows "{} \<notin> p" 
  using assms is_partition_def by fast

lemma l2a:
  fixes elem::'a
    and P::"'a set set"
  assumes partition: "is_partition P"
      and elem: "elem \<in> \<Union> P" 
  shows "P \<in> coarser_partitions_with elem (partition_without elem P)"
    (is "P \<in> coarser_partitions_with elem ?Q")
proof -
  let ?remove = "%X . X - {elem}" (* function that removes elem out of a set *)
  obtain Y (* the equivalence class of elem *)
    where elem_eq_class: "elem \<in> Y" and elem_eq_class': "Y \<in> P" using elem by blast
  let ?elem_neq_classes = "P - {Y}" (* those equivalence classes in which elem is not *)
  have P_wrt_elem: "P = ?elem_neq_classes \<union> {Y}" using elem_eq_class' by blast
  let ?elem_eq = "Y - {elem}" (* other elements equivalent to elem *)
  have Y_elem_eq: "?remove ` {Y} = {?elem_eq}" by fast
  (* those equivalence classes, in which elem is not, form a partition *)
  have elem_neq_classes_part: "is_partition ?elem_neq_classes" using subset_is_partition partition by blast
  have elem_eq_wrt_P: "?elem_eq \<in> ?remove ` P" using elem_eq_class' by blast
  
  {
    (* consider an equivalence class W, in which elem is not *)
    fix W assume W_eq_class: "W \<in> ?elem_neq_classes"
    then have "elem \<notin> W" using elem_eq_class elem_eq_class' partition is_partition_def by fast
    then have "?remove W = W" by simp
  }
  then have elem_neq_classes_id: "?remove ` ?elem_neq_classes = ?elem_neq_classes" by fastforce

  have Q_unfolded: "?Q = (?remove ` P) - {{}}" unfolding partition_without_def using image_Collect_mem by blast
  also have "\<dots> = (?remove ` (?elem_neq_classes \<union> {Y})) - {{}}" using P_wrt_elem by presburger
  also have "\<dots> = ?elem_neq_classes \<union> {?elem_eq} - {{}}"
    using elem_eq_class' partition_without_def image_union Y_elem_eq elem_neq_classes_id
    by smt
  finally have Q_wrt_elem: "?Q = ?elem_neq_classes \<union> {?elem_eq} - {{}}" .

  have "?elem_eq = {} \<or> ?elem_eq \<notin> P"
    using elem_eq_class elem_eq_class' partition is_partition_def
    by (smt Diff_Int_distrib2 Diff_iff Int_absorb empty_Diff insert_iff)
  then have "?elem_eq \<notin> P" using partition no_empty_eq_class by metis
  then have 0: "?elem_neq_classes - {?elem_eq} = ?elem_neq_classes" by fastforce

  show ?thesis
  proof cases
    assume "?elem_eq \<notin> ?Q"
    hence "?elem_eq \<in> {{}}" using elem_eq_wrt_P Q_unfolded by (metis DiffI)
    hence 9: "?elem_eq = {} \<and> Y = {elem}" using elem_eq_class by fast
    hence "?Q = ?elem_neq_classes - {{}}" using Q_wrt_elem is_partition_def assms by force
    hence 10: "?Q = ?elem_neq_classes" using no_empty_eq_class elem_neq_classes_part by blast
    then have "insert {elem} ?Q = P" using 9 elem_eq_class' by fast
    then show ?thesis using coarser_partitions_with_def by (metis insertI1)    
  next
    assume True: "\<not> ?elem_eq \<notin> ?Q"
    hence "?elem_eq \<noteq> {}" using no_empty_eq_class partition_without_is_partition assms by metis
    hence 12: "?elem_neq_classes \<union> {?elem_eq} - {{}} = ?elem_neq_classes \<union> {?elem_eq}" using no_empty_eq_class elem_neq_classes_part assms by blast
    have "insert_into_member elem ({?elem_eq} \<union> ?elem_neq_classes) (?elem_eq) = ({?elem_eq} \<union> ?elem_neq_classes) - {?elem_eq} \<union> {?elem_eq \<union> {elem}} " 
    using insert_into_member_def assms 0 by metis
    hence "insert_into_member elem ({?elem_eq} \<union> ?elem_neq_classes) ?elem_eq = ({} \<union> ?elem_neq_classes) \<union> {?elem_eq \<union> {elem}}" 
      using 0 by force
    hence "insert_into_member elem ({?elem_eq} \<union> ?elem_neq_classes) ?elem_eq = ?elem_neq_classes \<union> {Y}" using elem_eq_class by blast
    hence "?elem_neq_classes \<union> {Y} = insert_into_member elem ?Q ?elem_eq" using Q_wrt_elem 12 partition_without_def by force
    hence "{Y} \<union> ?elem_neq_classes \<in> insert_into_member elem ?Q ` ?Q" using True by blast
    hence "{Y} \<union> ?elem_neq_classes \<in> coarser_partitions_with elem ?Q" using coarser_partitions_with_def by (metis insertCI)
    then show ?thesis using P_wrt_elem by simp
  qed
qed

definition mypred ::" 'a => nat => bool" where "mypred x n = 
(\<forall> X::('a list) . (length X=n \<and> distinct X \<longrightarrow> 
all_partitions_classical (set X) = all_partitions_of_list X))"

lemma indstep: fixes x::"'a" fixes n::nat assumes "mypred x n" shows "mypred x (Suc n)"   
proof -
  let ?l = "all_partitions_of_list" let ?c = "all_partitions_classical" 
  let ?ch = "coarser_partitions_with" let ?P="is_partition" let ?Q="is_partition_of"
  have indhyp: "\<forall> X::('a list) . length X = n \<and> distinct X \<longrightarrow> (?c (set X) = ?l X)" 
  using mypred_def assms by fast
  (* what's the difference with def l == "allpartitionsoflist" (which doesn't work)?? *)
  have "\<forall> X::('a list) . ((length X=Suc n \<and> distinct X) \<longrightarrow> 
  (all_partitions_classical (set X) = all_partitions_of_list X))" 
  proof 
  fix X2::"'a list"
  let ?e = "hd X2" let ?f = "partition_without ?e" let ?n2 = "length X2" 
  let ?X1="tl X2" (* could use drop or sublist instead of tl *)
  show "(?n2=Suc n \<and> distinct X2) \<longrightarrow> (?c (set X2) = ?l X2)"
  proof
    assume a10: "?n2 = Suc n \<and> distinct X2"
    hence "X2=[?e]@?X1" 
    by (metis append_Cons append_Nil hd.simps length_Suc_conv tl.simps(2))
    hence 2: "X2=?e # ?X1" by fastforce
    have 13: "length ?X1=n" using a10 2 assms  
    by (metis diff_Suc_1 length_tl)
    have a12: "distinct ?X1" using a10 by (metis distinct_tl)
    hence "\<not> {?e} \<subseteq> set ?X1" using 2 a10 by (metis distinct.simps(2) insert_subset)
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
      hence 22: "?P p2" using partition_extension3 a9 19 by fast
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

theorem partadequacy: fixes l assumes "distinct l" shows 
"all_partitions_of_list l = all_partitions_classical (set l)" 
using l14 mypred_def assms by fast

definition all_partitions where "all_partitions X = all_partitions_of_list (sorted_list_of_set X)"

corollary fixes X assumes "finite X" shows 
"all_partitions X = all_partitions_classical X" 
unfolding all_partitions_def
using partadequacy assms by (metis sorted_list_of_set)
(* all_partitions internally works with a list representing a set
   (this allows us to use the recursive function all_partitions_of_list).
   For a list with repetitions we can only guarantee compliance
   once we establish norepetitions. *)

end
