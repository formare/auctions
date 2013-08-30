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
imports Main SetUtils ListUtils
begin

text {*
The algorithmic computation of all partitions of a set in @{text all_partitions_of_list} works as
in the following example:
\begin{itemize}
\item Set: $\{\a}$\\
  Partitions: $\{\{a\}\}$
\item Set: $\{a,b\}$
  Partitions: $\{\{a\}, \{b\}\}, \{\{a, b\}\}$
\item Set: $\{a,b,c\}$
  Partitions: $\{\{a\}, \{b\}, \{c\}\}, \{\{a,b\}, \{c\}\}, \{\{a,c\}, \{b\}\}, \{\{a\}, \{c,b\}\}, \{\{a,b,c\}\}$
\end{itemize}

BTW, the number of partitions of a set (same as the number of equivalence relations on the set) is known as 
\href{http://en.wikipedia.org/wiki/Bell_number}{Bell number}.
*}

text {* @{text P} is a partition of some set. *}
definition is_partition where
"is_partition P = (\<forall> x\<in>P . \<forall> y\<in> P . (x \<inter> y \<noteq> {} \<longleftrightarrow> x=y))"
(* alternative, less concise formalisation:
"is_partition P = (\<forall> ec1 \<in> P . ec1 \<noteq> {} \<and> (\<forall> ec2 \<in> P - {ec1}. ec1 \<inter> ec2 = {}))"
*)

text {* A subset of a partition is also a partition (but, note: only of a subset of the original set) *}
lemma subset_is_partition:
  assumes subset: "P \<subseteq> Q"
      and partition: "is_partition Q"
  shows "is_partition P"
proof -
  {
    fix x y assume "x \<in> P \<and> y \<in> P"
    then have "x \<in> Q \<and> y \<in> Q" using subset by fast
    then have "x \<inter> y \<noteq> {} \<longleftrightarrow> x = y" using partition unfolding is_partition_def by force
  }
  then show ?thesis unfolding is_partition_def by force
qed

(* TODO CL: document if used *)
lemma remove_from_eq_class_preserves_disjoint:
  fixes elem::'a
    and X::"'a set"
    and P::"'a set set"
  assumes partition: "is_partition P"
      and eq_class: "X \<in> P"
      and elem: "elem \<in> X"
  shows "X - {elem} \<notin> P"
using assms using is_partition_def
by (smt Diff_iff Int_Diff Int_absorb Int_commute insertCI)
(* This was very hard to find for sledgehammer *)

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

lemma no_empty_eq_class:
  assumes "is_partition p"
  shows "{} \<notin> p" 
  using assms is_partition_def by fast

text {* @{text P} is a partition of the set @{text A}. *}
definition is_partition_of where "is_partition_of P A = (\<Union> P = A \<and> is_partition P)"


text {* The empty set is a partition of the empty set. *}
lemma emptyset_part_emptyset1:
  shows "is_partition_of {} {}" 
  unfolding is_partition_of_def is_partition_def by fast

text {* Any partition of the empty set is empty. *}
lemma emptyset_part_emptyset2:
  assumes "is_partition_of P {}"
  shows "P = {}"
  using assms is_partition_def is_partition_of_def by fast

text {* classical set-theoretical definition of ``all partitions of a set @{text A}'' *}
definition all_partitions where 
"all_partitions A = {P . is_partition_of P A}"

text {* The set of all partitions of the empty set only contains the empty set.
  We need this to prove the base case of @{text all_partitions_paper_equiv_alg}. *}
lemma emptyset_part_emptyset3:
  shows "all_partitions {} = {{}}"
  unfolding all_partitions_def
  using emptyset_part_emptyset1 emptyset_part_emptyset2
  by fast

(* MC: Here is some new material.  Next step: integrate new partitions definitions into auctions 
   (i.e. nVCG_CaseChecker.thy) *)
(* MC: A further, proof-friendlier way of computing partitions is introduced: 
   everything's a set, except the very initial input, which is a list 
   (of elements) because I don't know how to do recursive definitions 
   on finite sets.
   CL@MC: There is a predicate Finite_Set.finite, which is defined inductively (search for 
   "inductive finite" in Finite_Set.thy, but it is not defined as an algebraic _datatype_ and 
   therefore doesn't work with recursive _functions_.
   Then equivalence with all_partitions is inductively shown *)
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
where "insert_into_member new_el Sets S = insert (S \<union> {new_el}) (Sets - {S})"

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
  then show ?thesis unfolding insert_into_member_def by simp
qed

(* TODO CL: if we end up preferring this over insert_into_member, document it.
   Rationale for this variant and for everything that depends on it:
   While it is possible to computationally enumerate "all partitions of a set" as
   "'a set set set", we need a list representation to apply further computational
   functions to partitions.  Because of the way we construct partitions (using functions
   such as all_coarser_partitions_with below) it is not sufficient to simply use 
   "'a set set list", but we need "'a set list list".  This is because it is hard 
   to impossible to convert a set to a list, whereas it is easy to convert a list to a set. *)
definition insert_into_member_list
:: "'a \<Rightarrow> 'a set list \<Rightarrow> 'a set \<Rightarrow> 'a set list"
where "insert_into_member_list new_el Sets S = (S \<union> {new_el}) # (remove1 S Sets)"

(* TODO CL: If we end up using this, document it *)
lemma insert_into_member_list_alt:
  fixes new_el::'a
    and Sets::"'a set list"
    and S::"'a set"
  assumes "distinct Sets"
  shows "set (insert_into_member_list new_el Sets S) = insert_into_member new_el (set Sets) S"
unfolding insert_into_member_list_def insert_into_member_def
using assms
by simp

lemma insert_into_member_partition1:
  fixes elem::'a
    and P::"'a set set"
    and eq_class::"'a set"
  (* no need to assume "eq_class \<in> P" *)
  shows "\<Union> insert_into_member elem P eq_class = \<Union> insert (eq_class \<union> {elem}) (P - {eq_class})"
    unfolding insert_into_member_def
    by fast

(* TODO CL: if we end up preferring this over insert_into_member_partition1, document it *)
lemma insert_into_member_partition1_list:
  fixes elem::'a
    and P::"'a set list"
    and eq_class::"'a set"
  (* no need to assume "eq_class \<in> P" *)
  shows "\<Union> set (insert_into_member_list elem P eq_class) = \<Union> insert (eq_class \<union> {elem}) (set (remove1 eq_class P))"
    unfolding insert_into_member_list_def
    by force

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

(* TODO CL: if we end up preferring this over coarser_partitions_with, document it *)
definition coarser_partitions_with_list ::"'a \<Rightarrow> 'a set list \<Rightarrow> 'a set list list"
where "coarser_partitions_with_list new_el P = 
  (* Let 'part' be a partition of a set 'Set',
     and suppose new_el \<notin> Set, i.e. {new_el} \<notin> part,
     then the following constructs a partition of 'Set \<union> {new_el}' obtained by
     inserting a new equivalence class {new_el} and leaving all previous equivalence classes unchanged. *)
  ({new_el} # P)
  #
  (* Let 'part' be a partition of a set 'Set',
     and suppose new_el \<notin> Set,
     then the following constructs
     the set of those partitions of 'Set \<union> {new_el}' obtained by
     inserting new_el into one equivalence class of 'part' at a time. *)
  (map ((insert_into_member_list new_el P)) P)"

(* TODO CL: If we end up using this, document it *)
lemma coarser_partitions_with_list_alt:
  assumes "distinct P"
  shows "set (map set (coarser_partitions_with_list new_el P)) = coarser_partitions_with new_el (set P)"
proof -
  have "set (map set (coarser_partitions_with_list new_el P)) = set (map set (({new_el} # P) # (map ((insert_into_member_list new_el P)) P)))"
    unfolding coarser_partitions_with_list_def ..
  also have "\<dots> = insert (insert {new_el} (set P)) ((set \<circ> (insert_into_member_list new_el P)) ` set P)"
    by simp
  also have "\<dots> = insert (insert {new_el} (set P)) ((insert_into_member new_el (set P)) ` set P)"
    using assms insert_into_member_list_alt by (metis comp_apply)
  finally show ?thesis unfolding coarser_partitions_with_def .
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
    using assms unfolding coarser_partitions_with_def by fast
  {
    fix eq_class assume eq_class_in_P: "eq_class \<in> P"
    have "\<Union> insert (eq_class \<union> {elem}) (P - {eq_class}) = ?S \<union> (eq_class \<union> {elem})"
      using insert_into_member_partition1
      by (metis Sup_insert Un_commute Un_empty_right Un_insert_right insert_Diff_single)
    with eq_class_in_P have "\<Union> insert (eq_class \<union> {elem}) (P - {eq_class}) = ?S \<union> {elem}" by blast
    then have "\<Union> insert_into_member elem P eq_class = ?S \<union> {elem}"
      using insert_into_member_partition1
      by (rule subst)
  }
  then show ?thesis using Q_cases by blast
qed

(* TODO CL: if we end up preferring this over coarser_partitions_covers_list, document it *)
lemma coarser_partitions_covers_list:
  fixes elem::'a
    and P::"'a set list"
    and Q::"'a set list"
  assumes Q_coarser: "Q \<in> set (coarser_partitions_with_list elem P)"
      and distinctP: "distinct P"
  shows "\<Union> set Q = insert elem (\<Union> set P)"
proof -
  from Q_coarser have "set Q \<in> set (map set (coarser_partitions_with_list elem P))" by simp
  with distinctP have "set Q \<in> coarser_partitions_with elem (set P)"
    using coarser_partitions_with_list_alt by fast
  then show ?thesis by (rule coarser_partitions_covers)
qed
(* Deleted the previous proof, which did not use coarser_partitions_with_list_alt
   and therefore needed a lost of manual list-to-set rewriting work. *)

text {* Removes the element @{text elem} from every set in @{text P}, and removes from @{text P} any
  remaining empty sets.  This function is intended to be applied to partitions, i.e. @{text elem}
  occurs in at most one set.  @{text "partition_without e"} reverses @{text "coarser_partitions_with e"}.
@{text coarser_partitions_with} is one-to-many, while this is one-to-one, so we can think of a tree relation,
where coarser partitions of a set @{text "S \<union> {elem}"} are child nodes of one partition of @{text S}. *}
definition partition_without :: "'a \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
where "partition_without elem P = (\<lambda>X . X - {elem}) ` P - {{}}"
(* Set comprehension notation { x - {elem} | x . x \<in> P } would look nicer but is harder to do proofs about *)

(* TODO CL: if we end up preferring this over partition_without, document it *)
definition partition_without_list :: "'a \<Rightarrow> 'a set list \<Rightarrow> 'a set list"
where "partition_without_list elem P = remove1 {} (map (\<lambda>x . x - {elem}) P)"

lemma remove_elem_inj:
  fixes elem::'a
    and P::"'a set list"
  assumes partition: "is_partition (set P)"
  shows "inj_on (\<lambda>X . X - {elem}) (set P)" (is "inj_on ?remove_elem ?Q")
proof (rule inj_onI)
  fix X Y assume X: "X \<in> set P" and Y: "Y \<in> set P"
  assume im_eq: "?remove_elem X = ?remove_elem Y"
  from partition have is_partition_unfolded: "\<forall> X \<in> set P . \<forall> Y \<in> set P . (X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y)"
    unfolding is_partition_def .
  from X Y partition have "\<exists>u. (u \<in> X \<and> u \<in> Y) \<and> u \<notin> {}"
    by (metis (mono_tags) empty_iff equals0I im_eq member_remove no_empty_eq_class remove_def)
  then show "X = Y" using X Y is_partition_unfolded by (metis IntI)
qed

(* TODO CL: If we end up using this, document it *)
lemma partition_without_list_distinct:
  fixes elem::'a
    and P::"'a set list"
  assumes distinct: "distinct P"
      and partition: "is_partition (set P)"
  shows "distinct (partition_without_list elem P)"
proof -
  let ?remove_elem = "\<lambda>X . X - {elem}"
  from distinct show ?thesis
    using distinct_map partition remove_elem_inj
    unfolding partition_without_list_def by (metis distinct_remove1)
qed  

(* TODO CL: If we end up using this, document it *)
lemma partition_without_list_alt:
  fixes elem::'a
    and P::"'a set list"
  assumes distinct: "distinct P"
      and partition: "is_partition (set P)"
  shows "set (partition_without_list elem P) = partition_without elem (set P)"
proof -
  let ?remove_elem = "\<lambda>X . X - {elem}"
  have "set (partition_without_list elem P) = set (remove1 {} (map ?remove_elem P))"
    unfolding partition_without_list_def
    by fast
  also have "\<dots> = set (removeAll {} (map ?remove_elem P))"
    using distinct partition remove_elem_inj
    by (metis distinct_map set_remove1_eq set_removeAll)
  also have "\<dots> = set (map ?remove_elem P) - {{}}" by (rule set_removeAll)
  also have "\<dots> = ?remove_elem ` set P - {{}}" by (metis image_set)
  finally show ?thesis unfolding partition_without_def .
qed

lemma partition_without_covers:
  fixes elem::'a
    and P::"'a set set"
  shows "\<Union> partition_without elem P = \<Union> P - {elem}"
proof -
  have "\<Union> partition_without elem P = \<Union> ((\<lambda>x . x - {elem}) ` P - {{}})"
    unfolding partition_without_def by fast
  also have "\<dots> = \<Union> P - {elem}" by blast
  finally show ?thesis .
qed

(* TODO CL: if we end up preferring this over partition_without_covers, document it *)
lemma partition_without_covers_list:
  fixes elem::'a
      and P::"'a set list"
  assumes distinct: "distinct P"
      and partition: "is_partition (set P)"
  shows "\<Union> set (partition_without_list elem P) = \<Union> (set P) - {elem}"
proof -
  let ?remove_elem = "\<lambda>X . X - {elem}"
  have "set (partition_without_list elem P) = partition_without elem (set P)"
    using distinct partition partition_without_list_alt
    unfolding partition_without_def by metis
  (* TODO CL: find out why solve_direct's results don't work with by (rule \<dots>)
     http://stackoverflow.com/questions/18511720/how-can-i-use-rules-suggested-by-solve-direct-by-rule-doesnt-always-work *)
  then show ?thesis using partition_without_covers by (rule ssubst)
qed

lemma super_eq_class:
  assumes "X \<in> partition_without elem P"
  obtains Z where "Z \<in> P" and "X = Z - {elem}"
proof -
  from assms have "X \<in> (\<lambda>X . X - {elem}) ` P - {{}}" unfolding partition_without_def .
  then obtain Z where Z_in_P: "Z \<in> P" and Z_sup: "X = Z - {elem}"
    by (metis (lifting) Diff_iff image_iff)
  then show ?thesis ..
qed

lemma partition_without_is_partition:
  fixes elem::'a
    and P::"'a set set"
  assumes "is_partition P"
  shows "is_partition (partition_without elem P)" (is "is_partition ?Q")
proof -   
  have "\<forall> x1 \<in> ?Q. \<forall> x2 \<in> ?Q. x1 \<inter> x2 \<noteq> {} \<longleftrightarrow> x1 = x2"
  proof 
    fix x1 assume x1_in_Q: "x1 \<in> ?Q"
    then obtain z1 where z1_in_P: "z1 \<in> P" and z1_sup: "x1 = z1 - {elem}"
      by (rule super_eq_class)
    have x1_non_empty: "x1 \<noteq> {}" using x1_in_Q partition_without_def by fast
    show "\<forall> x2 \<in> ?Q. x1 \<inter> x2 \<noteq> {} \<longleftrightarrow> x1 = x2" 
    proof
      fix x2 assume "x2 \<in> ?Q"
      then obtain z2 where z2_in_P: "z2 \<in> P" and z2_sup: "x2 = z2 - {elem}"
        by (rule super_eq_class)
      have "x1 \<inter> x2 \<noteq> {} \<longrightarrow> x1 = x2"
      proof
        assume "x1 \<inter> x2 \<noteq> {}"
        then have "z1 \<inter> z2 \<noteq> {}" using z1_sup z2_sup by fast
        then have "z1 = z2" using z1_in_P z2_in_P assms unfolding is_partition_def by fast
        then show "x1 = x2" using z1_sup z2_sup by fast
      qed
      moreover have "x1 = x2 \<longrightarrow> x1 \<inter> x2 \<noteq> {}" using x1_non_empty by auto
      ultimately show "(x1 \<inter> x2 \<noteq> {}) \<longleftrightarrow> x1 = x2" by blast
    qed
  qed
  then show ?thesis unfolding is_partition_def .
qed

lemma partition_without_is_partition_list:
  fixes elem::'a
    and P::"'a set list"
  assumes distinct: "distinct P"
      and partition: "is_partition (set P)"
  shows "is_partition (set (partition_without_list elem P))"
proof -
  from distinct partition have "set (partition_without_list elem P) = partition_without elem (set P)"
    by (rule partition_without_list_alt)
  with partition show ?thesis using partition_without_is_partition by fastforce
qed

lemma coarser_partitions_inv_without:
  fixes elem::'a
    and P::"'a set set"
  assumes partition: "is_partition P"
      and elem: "elem \<in> \<Union> P" 
  shows "P \<in> coarser_partitions_with elem (partition_without elem P)"
    (is "P \<in> coarser_partitions_with elem ?Q")
proof -
  let ?remove_elem = "\<lambda>X . X - {elem}" (* function that removes elem out of a set *)
  obtain Y (* the equivalence class of elem *)
    where elem_eq_class: "elem \<in> Y" and elem_eq_class': "Y \<in> P" using elem ..
  let ?elem_neq_classes = "P - {Y}" (* those equivalence classes in which elem is not *)
  have P_wrt_elem: "P = ?elem_neq_classes \<union> {Y}" using elem_eq_class' by blast
  let ?elem_eq = "Y - {elem}" (* other elements equivalent to elem *)
  have Y_elem_eq: "?remove_elem ` {Y} = {?elem_eq}" by fast
  (* those equivalence classes, in which elem is not, form a partition *)
  have elem_neq_classes_part: "is_partition ?elem_neq_classes"
    using subset_is_partition partition
    by blast
  have elem_eq_wrt_P: "?elem_eq \<in> ?remove_elem ` P" using elem_eq_class' by blast
  
  { (* consider an equivalence class W, in which elem is not *)
    fix W assume W_eq_class: "W \<in> ?elem_neq_classes"
    then have "elem \<notin> W"
      using elem_eq_class elem_eq_class' partition is_partition_def
      by fast
    then have "?remove_elem W = W" by simp
  }
  then have elem_neq_classes_id: "?remove_elem ` ?elem_neq_classes = ?elem_neq_classes" by fastforce

  have Q_unfolded: "?Q = ?remove_elem ` P - {{}}"
    unfolding partition_without_def
    using image_Collect_mem
    by blast
  also have "\<dots> = ?remove_elem ` (?elem_neq_classes \<union> {Y}) - {{}}" using P_wrt_elem by presburger
  also have "\<dots> = ?elem_neq_classes \<union> {?elem_eq} - {{}}"
    using elem_eq_class' partition_without_def image_union Y_elem_eq elem_neq_classes_id
    by smt
  finally have Q_wrt_elem: "?Q = ?elem_neq_classes \<union> {?elem_eq} - {{}}" .

  have "?elem_eq = {} \<or> ?elem_eq \<notin> P"
    using elem_eq_class elem_eq_class' partition unfolding is_partition_def
    by (smt Diff_Int_distrib2 Diff_iff Int_absorb empty_Diff insert_iff)
  then have "?elem_eq \<notin> P"
    using partition no_empty_eq_class
    by metis
  then have elem_neq_classes: "?elem_neq_classes - {?elem_eq} = ?elem_neq_classes" by fastforce

  show ?thesis
  proof cases
    assume "?elem_eq \<notin> ?Q" (* the equivalence class of elem is not a member of ?Q = partition_without elem P *)
    then have "?elem_eq \<in> {{}}"
      using elem_eq_wrt_P Q_unfolded
      by (metis DiffI)
    then have Y_singleton: "Y = {elem}" using elem_eq_class by fast
    then have "?Q = ?elem_neq_classes - {{}}"
      using Q_wrt_elem
      by force
    then have "?Q = ?elem_neq_classes"
      using no_empty_eq_class elem_neq_classes_part
      by blast
    then have "insert {elem} ?Q = P"
      using Y_singleton elem_eq_class'
      by fast
    then show ?thesis unfolding coarser_partitions_with_def by auto
  next
    assume True: "\<not> ?elem_eq \<notin> ?Q"
    hence Y': "?elem_neq_classes \<union> {?elem_eq} - {{}} = ?elem_neq_classes \<union> {?elem_eq}"
      using no_empty_eq_class partition partition_without_is_partition
      by force
    have "insert_into_member elem ({?elem_eq} \<union> ?elem_neq_classes) ?elem_eq = insert (?elem_eq \<union> {elem}) (({?elem_eq} \<union> ?elem_neq_classes) - {?elem_eq})"
      unfolding insert_into_member_def ..
    also have "\<dots> = ({} \<union> ?elem_neq_classes) \<union> {?elem_eq \<union> {elem}}" using elem_neq_classes by force
    also have "\<dots> = ?elem_neq_classes \<union> {Y}" using elem_eq_class by blast
    finally have "insert_into_member elem ({?elem_eq} \<union> ?elem_neq_classes) ?elem_eq = ?elem_neq_classes \<union> {Y}" .
    then have "?elem_neq_classes \<union> {Y} = insert_into_member elem ?Q ?elem_eq"
      using Q_wrt_elem Y' partition_without_def
      by force
    then have "{Y} \<union> ?elem_neq_classes \<in> insert_into_member elem ?Q ` ?Q" using True by blast
    then have "{Y} \<union> ?elem_neq_classes \<in> coarser_partitions_with elem ?Q" unfolding coarser_partitions_with_def by simp
    then show ?thesis using P_wrt_elem by simp
  qed
qed

lemma coarser_partitions_inv_without_list:
  fixes elem::'a
    and P::"'a set list"
  assumes distinct: "distinct P"
      and partition: "is_partition (set P)"
      and elem: "elem \<in> \<Union> (set P)" 
  shows "set P \<in> set (map set (coarser_partitions_with_list elem (partition_without_list elem P)))"
proof -
  (* We actually shouldn't need this, but the proof below doesn't work by merely
     using partition_without_list_alt. *)
  from distinct partition have *: "set (partition_without_list elem P) = partition_without elem (set P)"
    by (rule partition_without_list_alt)

  from distinct partition
    have "distinct (partition_without_list elem P)"
    by (rule partition_without_list_distinct)
  then have "set (map set (coarser_partitions_with_list elem (partition_without_list elem P))) = coarser_partitions_with elem (set (partition_without_list elem P))"
    by (rule coarser_partitions_with_list_alt)
  also have "\<dots> = coarser_partitions_with elem (partition_without elem (set P))"
    using distinct partition * by simp
  finally have list_set_rel: "set (map set (coarser_partitions_with_list elem (partition_without_list elem P))) = coarser_partitions_with elem (partition_without elem (set P))" .

  from partition elem
    have "set P \<in> coarser_partitions_with elem (partition_without elem (set P))"
    using coarser_partitions_inv_without by simp
  with list_set_rel show ?thesis by fast
qed

definition all_coarser_partitions_with :: " 'a \<Rightarrow> 'a set set set \<Rightarrow> 'a set set set"
where "all_coarser_partitions_with elem Ps = \<Union> coarser_partitions_with elem ` Ps"

(* TODO CL: if we end up preferring this over all_coarser_partitions_with, document it *)
definition all_coarser_partitions_with_list :: " 'a \<Rightarrow> 'a set list list \<Rightarrow> 'a set list list"
where "all_coarser_partitions_with_list elem Ps = concat (map (coarser_partitions_with_list elem) Ps)"

lemma all_coarser_partitions_with_list_alt:
  fixes elem::'a
    and Ps::"'a set list list"
  assumes distinct: "\<forall> P \<in> set Ps . distinct P"
  shows "set (map set (all_coarser_partitions_with_list elem Ps)) = all_coarser_partitions_with elem (set (map set Ps))"
    (is "?list_expr = ?set_expr")
proof -
  have "?list_expr = set (map set (concat (map (coarser_partitions_with_list elem) Ps)))"
    unfolding all_coarser_partitions_with_list_def ..
  also have "\<dots> = set ` (\<Union> x \<in> (coarser_partitions_with_list elem) ` (set Ps) . set x)" by simp
    (* This and other intermediate results may not be easy to understand.  I obtained them by 
       conflating multiple “by <simple_method>” steps into one. *)
  also have "\<dots> = set ` (\<Union> x \<in> { coarser_partitions_with_list elem P | P . P \<in> set Ps } . set x)"
    by (metis image_Collect_mem)
  also have "\<dots> = \<Union> { set (map set (coarser_partitions_with_list elem P)) | P . P \<in> set Ps }" by auto
  also have "\<dots> = \<Union> { coarser_partitions_with elem (set P) | P . P \<in> set Ps }"
    using distinct coarser_partitions_with_list_alt by fast
  also have "\<dots> = \<Union> coarser_partitions_with elem ` (set ` (set Ps))" by (metis image_Collect_mem image_image)
  also have "\<dots> = \<Union> coarser_partitions_with elem ` (set (map set Ps))" by simp
  also have "\<dots> = ?set_expr" unfolding all_coarser_partitions_with_def ..
  finally show ?thesis .
qed

fun all_partitions_of_list :: "'a list \<Rightarrow> 'a set set set"
where 
"all_partitions_of_list [] = {{}}" |
"all_partitions_of_list (e # X) = all_coarser_partitions_with e (all_partitions_of_list X)"

(* TODO CL: if we end up preferring this over all_partitions_of_list, document it *)
fun all_partitions_of_list_list :: "'a list \<Rightarrow> 'a set list list"
where 
"all_partitions_of_list_list [] = [[]]" |
"all_partitions_of_list_list (e # X) = all_coarser_partitions_with_list e (all_partitions_of_list_list X)"

lemma all_partitions_of_list_list_distinct:
  "\<forall> P \<in> set (all_partitions_of_list_list xs) . distinct P" sorry

lemma all_partitions_of_list_list_alt:
  assumes distinct: "distinct xs"
  shows "set (map set (all_partitions_of_list_list xs)) = all_partitions_of_list xs"
proof (induct xs)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  have "set (map set (all_partitions_of_list_list (x # xs))) = set (map set (all_coarser_partitions_with_list x (all_partitions_of_list_list xs)))"
    by simp
  also have "\<dots> = all_coarser_partitions_with x (set (map set (all_partitions_of_list_list xs)))"
    using all_partitions_of_list_list_distinct
    by (rule all_coarser_partitions_with_list_alt)
  also have "\<dots> = all_coarser_partitions_with x (all_partitions_of_list xs)"
    using Cons.hyps by force
  also have "\<dots> = all_partitions_of_list (x # xs)" by simp
  finally show ?case .
qed

text {* The induction step of @{text all_partitions_paper_equiv_alg} *}
lemma all_partitions_paper_equiv_alg_indstep:
  fixes n::nat
  assumes "\<forall> X::'a list . length X = n \<and> distinct X \<longrightarrow> all_partitions (set X) = all_partitions_of_list X"
  shows "\<forall> X::'a list . length X = Suc n \<and> distinct X \<longrightarrow> all_partitions (set X) = all_partitions_of_list X"   
proof
  fix X :: "'a list"
  show "length X = Suc n \<and> distinct X \<longrightarrow> all_partitions (set X) = all_partitions_of_list X"
  proof
    assume assm: "length X = Suc n \<and> distinct X"
    then have length: "length X = Suc n" and distinct: "distinct X" by simp_all
    from length have split_hd_tl: "X = (hd X) # tl X"
      by (metis Zero_neq_Suc hd.simps length_0_conv list.exhaust tl.simps(2))
    then have length_tl: "length (tl X) = n"
      using length assms by simp
    have distinct_tl: "distinct (tl X)" using distinct by (rule distinct_tl)
    then have hd_notin_tl: "hd X \<notin> set (tl X)"
      using split_hd_tl distinct by (metis distinct.simps(2))

    show "all_partitions (set X) = all_partitions_of_list X"
    proof (rule equalitySubsetI)
      fix P
      let ?P_without_hd_X = "partition_without (hd X) P"
      have P_partitions_exc_hd: "\<Union> ?P_without_hd_X = \<Union> P - {hd X}" using partition_without_covers .

      assume "P \<in> all_partitions (set X)"
      then have is_partition_of: "is_partition_of P (set X)" unfolding all_partitions_def ..
      then have is_partition: "is_partition P" by (metis is_partition_of_def)
      from is_partition_of have P_covers: "\<Union> P = set X" unfolding is_partition_of_def by simp
      have "is_partition_of ?P_without_hd_X (set (tl X))"
        unfolding is_partition_of_def
        using is_partition partition_without_is_partition split_hd_tl P_partitions_exc_hd partition_without_covers hd_notin_tl P_covers
        by (metis Diff_insert_absorb List.set.simps(2))
      then have p_list: "?P_without_hd_X \<in> all_partitions_of_list (tl X)"
        using assms all_partitions_def length_tl distinct_tl by fast
      then have "P \<in> (coarser_partitions_with (hd X)) ?P_without_hd_X"
        using coarser_partitions_inv_without is_partition P_covers assm split_hd_tl
        by (metis (full_types) not_Cons_self2 remove1.simps(2) remove1_idem)
      then have "P \<in> \<Union> coarser_partitions_with (hd X) ` all_partitions_of_list (tl X)" using p_list by blast
      then show "P \<in> all_partitions_of_list X"
        using split_hd_tl all_coarser_partitions_with_def
        by (metis all_partitions_of_list.simps(2))
    next
      fix P
      assume "P \<in> all_partitions_of_list X"
      then have "P \<in> all_coarser_partitions_with (hd X) (all_partitions_of_list (tl X))"
        using split_hd_tl by (metis all_partitions_of_list.simps(2))
      then have "P \<in> \<Union> coarser_partitions_with (hd X) ` (all_partitions_of_list (tl X))"
        unfolding all_coarser_partitions_with_def .
      then obtain Y
        where P_in_Y: "P \<in> Y"
        and Y_coarser: "Y \<in> coarser_partitions_with (hd X) ` (all_partitions_of_list (tl X))" ..
      from Y_coarser obtain Q
        where Q_part_tl: "Q \<in> all_partitions_of_list (tl X)"
        and Y_coarser': "Y = coarser_partitions_with (hd X) Q" ..
      from P_in_Y Y_coarser' have P_wrt_Q: "P \<in> coarser_partitions_with (hd X) Q" by fast
      have "all_partitions (set (tl X)) = all_partitions_of_list (tl X)"
        using assms distinct_tl split_hd_tl length length_tl by presburger
      then have "Q \<in> all_partitions (set (tl X))"
        using Q_part_tl assms by blast
      then have "is_partition_of Q (set (tl X))" unfolding all_partitions_def ..
      then have "is_partition Q" and Q_covers: "\<Union> Q = set (tl X)" 
        unfolding is_partition_of_def by simp_all
      then have P_partition: "is_partition P"
        using partition_extension3 P_wrt_Q hd_notin_tl by fast
      have "\<Union> P = (set (tl X)) \<union> {hd X}"
        using Q_covers P_in_Y Y_coarser' coarser_partitions_covers by fast
      then have "\<Union> P = set X"
        using hd_notin_tl split_hd_tl P_wrt_Q Q_covers coarser_partitions_covers
        by (metis (full_types) List.set.simps(2))
      then have "is_partition_of P (set X)"
        using P_partition unfolding is_partition_of_def by blast
      then show "P \<in> all_partitions (set X)" unfolding all_partitions_def ..
    qed
  qed
qed

text {* The paper-like definition @{text all_partitions} and the algorithmic definition
  @{text all_partitions_of_list} are equivalent. *}
theorem all_partitions_paper_equiv_alg:
  fixes l::"'a list"
  assumes "distinct l"
  shows "all_partitions_of_list l = all_partitions (set l)"
proof -
  {
    fix n::nat
    have "\<forall> l::'a list . length l = n \<and> distinct l \<longrightarrow> 
      all_partitions (set l) = all_partitions_of_list l"
    proof (induct n)
    case 0
      show ?case using emptyset_part_emptyset3
        by (metis all_partitions_of_list.simps(1) length_0_conv set_empty2)
    case (Suc n)
      assume "\<forall> X::'a list . length X = n \<and> distinct X \<longrightarrow> all_partitions (set X) = all_partitions_of_list X"
      then show ?case by (rule all_partitions_paper_equiv_alg_indstep)
    qed
  }
  then show ?thesis using assms by simp
qed

text {* The function that we will be using in practice to compute all partitions of a set,
  a set-oriented frontend to @{text all_partitions_of_list} *}
definition all_partitions_alg :: "'a\<Colon>linorder set \<Rightarrow> 'a set set set"
where "all_partitions_alg X = all_partitions_of_list (sorted_list_of_set X)"

corollary [code_unfold]:
  fixes X
  assumes "finite X"
  shows "all_partitions X = all_partitions_alg X"
  unfolding all_partitions_alg_def
  using all_partitions_paper_equiv_alg assms by (metis sorted_list_of_set)
(* all_partitions internally works with a list representing a set
   (this allows us to use the recursive function all_partitions_of_list).
   For a list with repetitions we can only guarantee compliance
   once we establish norepetitions. *)

section {* Unused alternative definitions *}

text {* @{text E} is the set of all equivalence relations on the set @{text X}. *}
definition isEquivSet :: "('a \<times> 'a) set set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "isEquivSet E X \<longleftrightarrow> (\<forall> e . e \<in> E \<longleftrightarrow> equiv X e)"

text {* another set-theoretical, non-computable definition of ``all partitions of a set @{text A}'':
  the set of all quotients of @{text A} w.r.t.\ some equivalence relation @{text R} *}
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

text {* an entirely list-based algorithm, which serves as an alternative to 
  @{text all_partitions_of_list}, @{text all_coarser_partitions_with}, 
  @{text coarser_partitions_with}, @{text insert_into_member} *}
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

text {* frontend to @{text all_partitions_fun_list}, turns the @{text "'a set list list"}
  returned by that function into a @{text "'a set set set"} *}
fun all_partitions_fun :: "'a\<Colon>linorder set \<Rightarrow> 'a set set set"
  where "all_partitions_fun A = set (map set (all_partitions_fun_list (sorted_list_of_set A)))"

(* TODO CL: do unused_thms and remove some list\<leftrightarrow>set theorems, possibly all except *_alt *)

end
