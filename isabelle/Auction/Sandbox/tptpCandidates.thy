(* from Partition.thy *)

lemma subset_is_non_overlapping:
  assumes subset: "P \<subseteq> Q" and 
          non_overlapping: "is_non_overlapping Q"
  shows "is_non_overlapping P"
(* CL: The following takes 387 ms with Isabelle2013-1-RC1:
   by (metis is_non_overlapping_def non_overlapping set_rev_mp subset). MC: possibly useful for TPTP *)
proof -
  {
    fix X Y assume "X \<in> P \<and> Y \<in> P"
    then have "X \<in> Q \<and> Y \<in> Q" using subset by fast
    then have "X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y" using non_overlapping unfolding is_non_overlapping_def by force
  }
  then show ?thesis unfolding is_non_overlapping_def by force
qed

text {* The family that results from removing one element from an equivalence class of a non-overlapping family is not otherwise a member of the family. *}
lemma remove_from_eq_class_preserves_disjoint:
      fixes elem::'a
        and X::"'a set"
        and P::"'a set set"
      assumes non_overlapping: "is_non_overlapping P"
        and eq_class: "X \<in> P"
        and elem: "elem \<in> X"
      shows "X - {elem} \<notin> P"
  using assms Int_Diff is_non_overlapping_def Diff_disjoint Diff_eq_empty_iff 
        Int_absorb2 insert_Diff_if insert_not_empty by (metis)


text {* The empty set is not element of a non-overlapping family. *}
lemma no_empty_in_non_overlapping:
  assumes "is_non_overlapping p"
  shows "{} \<notin> p"
(* CL: The following takes 36 ms with Isabelle2013-1-RC1:
   by (metis Int_iff all_not_in_conv assms is_non_overlapping_def). MC: possibly useful for TPTP *)
  using assms is_non_overlapping_def by fast

text {* Every element of the difference of a set @{term A} and another set @{term B} ends up in 
  an element of a partition of @{term A}, but not in an element of the partition of @{term "{B}"}. *}
lemma diff_elem_in_partition:
  assumes x: "x \<in> A - B"
      and part: "P partitions A"
  shows "\<exists> S \<in> P - { B } . x \<in> S"
(* Sledgehammer in Isabelle2013-1-RC1 can't do this within the default time limit. 
MC: possibly useful for TPTP *)
proof -
  from part x obtain X where "x \<in> X" and "X \<in> P"
    by (metis Diff_iff elem_in_partition)
  with x have "X \<noteq> B" by fast
  with `x \<in> X` `X \<in> P` show ?thesis by blast
qed

text {* A non-empty set ``is'' a partition of itself. *}
lemma set_partitions_itself:
  assumes "A \<noteq> {}"
  shows "{A} partitions A" unfolding is_partition_of_def is_non_overlapping_def
(* CL: the following takes 48 ms on my machine with Isabelle2013:
   by (metis Sup_empty Sup_insert assms inf_idem singletonE sup_bot_right). MC: possibly useful for TPTP *)
   
text {* an alternative characterization of the set partitioned by a partition obtained by 
  inserting an element into an equivalence class of a given partition (if @{term P}
  \emph{is} a partition) *}
lemma insert_into_member_partition1:
  fixes elem::'a
    and P::"'a set set"
    and set::"'a set"
  shows "\<Union> insert_into_member elem P set = \<Union> insert (set \<union> {elem}) (P - {set})"
(* CL: The following takes 12 ms in Isabelle2013-1-RC1:
   by (metis insert_into_member_def). MC: possibly useful for TPTP *)
    unfolding insert_into_member_def
    by fast
   


(* from CombinatorialAuction.thy *)
lemma allAllocationsInPowerset: 
  "allAllocations N \<Omega> \<subseteq> Pow (N \<times> (Pow \<Omega> - {{}}))" 
  by (metis PowI allocationPowerset subsetI)

lemma soldAllocationsFinite: 
  assumes "finite N" "finite \<Omega>" 
  shows "finite (soldAllocations N \<Omega>)"
  
corollary soldAllocationRestriction: 
  assumes "a \<in> soldAllocations N \<Omega>" 
  shows "a -- n \<in> soldAllocations (N-{n}) \<Omega>"
  

  
(* from UniformTieBreaking.thy *)

(* TPTP: This result links the concept of cardinality to the sum over a set: it is somehow a bridge between
set theory and economics (where we use setsum to calculate revenues)*)

corollary lm112: 
  assumes "Z \<subseteq> X \<union> Y" "finite Z" 
  shows "setsum (X <| Y) Z = card (Z \<inter> X)"
  using assms lm111 by (metis lm106 setsum_indicator_eq_card)

(* type conversion to real commutes *)
lemma lm095: 
  "summedBidSecond (real \<circ> ((bids:: _ => nat))) pair = real (summedBidSecond bids pair)" 
  by simp


  
  
  
  
  
(* from Argmax.thy *)

(* TPTP: this is a general fact about lists versus function application. *)
lemma map_commutes: fixes f::"'a => 'b" fixes Q::"'b => bool" fixes xs::"'a list" 
                    shows "[f n . n <- xs, Q (f n)] = [x <- (map f xs). Q x]"
      using map_commutes_a map_commutes_b structInduct by fast
  
(* TPTP: a general fact about Max *)      
lemma maxLemma: 
  assumes "x \<in> X" "finite X" 
  shows "Max (f`X) >= f x" 
  (is "?L >= ?R") using assms 
  by (metis (hide_lams, no_types) Max.coboundedI finite_imageI image_eqI)

(* from Universes.thy *)

(* The core step for injections bridging theorem *)
lemma lm101: 
  assumes "x \<notin> set xs" 
          "set (injections_alg xs Y) = injections (set xs) Y" 
          "finite Y" 
  shows    "set (injections_alg (x#xs) Y) = injections ({x} \<union> set xs) Y" 
  (is "?l=?r")

  
(* from MiscTools.thy *)

lemma lm024: 
  assumes "f \<circ> g = id" 
  shows "inj_on g UNIV" using assms 
  by (metis inj_on_id inj_on_imageI2)
  
lemma injectionPowerset: 
  assumes "inj_on f Y" "X \<subseteq> Y" 
  shows "inj_on (image f) (Pow X)"
  using assms lm025 by (metis subset_inj_on)

lemma pairDifference: 
  "{(x,X)}-{(x,Y)} = {x}\<times>({X}-{Y})" 
  by blast

(* triples a can be bracket in any way, i.e., (1st, (2nd, 3rd)) \<rightarrow> ((1st, 2nd), 3rd).*)
lemma lm050: 
  "inj_on  (%a. ((fst a, fst (snd a)), snd (snd a))) UNIV" 
  by (metis (lifting, mono_tags) Pair_fst_snd_eq Pair_inject injI)


lemma setsumPairsInverse: 
  assumes "runiq (P^-1)" 
  shows "setsum (f \<circ> snd) P = setsum f (Range P)" 
  using assms lm062 converse_converse rightUniqueInjectiveOnFirst rightUniqueInjectiveOnFirst
        setsum.reindex snd_eq_Range 
  by metis


lemma lm072: 
  "finite \<circ> finestpart = finite" 
  using finiteFinestpart by fastforce


(* A relation for the sum of all y\<in>Y of f(x,y) for a fixed x. *)
lemma sumCurry: 
  "setsum ((curry f) x) Y = setsum f ({x} \<times> Y)"  

lemma lm060: 
  "inj_on fst P = inj_on (snd\<circ>flip) P" 
  using lm058 by metis

lemma lm142: 
  assumes "trivial X" 
  shows "card (Pow X)\<in>{1,2}" 
  using trivial_empty_or_singleton card_Pow Pow_empty assms trivial_implies_finite
        cardinalityOneTheElemIdentity power_one_right the_elem_eq 
  by (metis insert_iff)
  

  
